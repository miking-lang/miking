package codegen;

import codegen.ClassWriterF;

import org.objectweb.asm.MethodVisitor;
import static org.objectweb.asm.Opcodes.*;
import org.objectweb.asm.Label;
import java.io.FileOutputStream;
import java.io.File;

import java.util.*;

import javax.swing.event.CaretEvent;
import javax.swing.text.FieldView;

//import org.objectweb.asm.util.CheckClassAdapter;

import com.fasterxml.jackson.databind.*;

class ClassfileMaker {
    //CheckClassAdapter cw;
    ClassWriterF cw;
    JsonNode classes;
    JsonNode interfaces;
    ClassWriterF iw;
    String pkg;
    Map<String, Label> labels;

    public ClassfileMaker(JsonNode json) {
        pkg = json.get("package").asText();
        labels = new HashMap<String, Label>();

        interfaces = json.get("interfaces");

        for (int i = 0; i < interfaces.size(); i++) {
            iw = new ClassWriterF(ClassWriterF.COMPUTE_MAXS+ClassWriterF.COMPUTE_FRAMES);
            JsonNode interf = interfaces.get(i);

            iw.visit(V1_5, ACC_PUBLIC + ACC_ABSTRACT + ACC_INTERFACE, pkg + interf.get("name").asText(), null, "java/lang/Object", null);

            JsonNode functions = interf.get("functions");
            for (int j = 0; j < functions.size(); j++) {
                JsonNode function = functions.get(j);
                iw.visitMethod(ACC_PUBLIC + ACC_ABSTRACT, function.get("name").asText(), function.get("descriptor").asText(), null, null);
            }
            iw.visitEnd();

            outputClassfile(interf.get("name").asText(), iw);
        }

        classes = json.get("classes");


        for (int i = 0; i < classes.size(); i++) {
            JsonNode c = classes.get(i);
            String[] interf = null;
            if (!c.get("implements").asText().equals("")) {
                interf = new String[] {c.get("implements").asText()};
            }

            cw = new ClassWriterF(ClassWriterF.COMPUTE_MAXS+ClassWriterF.COMPUTE_FRAMES);
            // version, access, name, signature, superName, String[] interfaces
            cw.visit(V1_5, ACC_PUBLIC + ACC_SUPER, pkg + c.get("name").asText(), null, "java/lang/Object", interf);

            if (c.get("name").asText().equals("Main")) {
                cw.visitField(ACC_PUBLIC+ACC_FINAL+ACC_STATIC, "random", "Ljava/util/Random;", null, null).visitEnd();
                cw.visitField(ACC_PUBLIC+ACC_FINAL+ACC_STATIC, "symbol", "L"+pkg+"GenSym;", null, null).visitEnd();
                cw.visitField(ACC_PUBLIC+ACC_STATIC, "argv", "Lscala/collection/immutable/Vector;", null, null).visitEnd();
                MethodVisitor mv = cw.visitMethod(ACC_STATIC, "<clinit>", "()V", null, null);
                mv.visitCode();
                mv.visitTypeInsn(NEW, "java/util/Random");
                mv.visitInsn(DUP);
                mv.visitMethodInsn(INVOKESPECIAL, "java/util/Random", "<init>", "()V", false);
                mv.visitFieldInsn(PUTSTATIC, pkg+"Main", "random", "Ljava/util/Random;");
                mv.visitTypeInsn(NEW, pkg+"GenSym");
                mv.visitInsn(DUP);
                mv.visitMethodInsn(INVOKESPECIAL, pkg+"GenSym", "<init>", "()V", false);
                mv.visitInsn(DUP);
                mv.visitLdcInsn(0);
                mv.visitFieldInsn(PUTFIELD, pkg+"GenSym", "symbolInt", "I");
                mv.visitFieldInsn(PUTSTATIC, pkg+"Main", "symbol", "L"+pkg+"GenSym;");
                mv.visitInsn(RETURN);
                mv.visitMaxs(0, 0);
                mv.visitEnd();
            }

            // create fields
            JsonNode fields = c.get("fields");
            for (int j = 0; j < fields.size(); j++) {
                JsonNode field = fields.get(j);
                String type = field.get("kind").asText();
                if (field.get("name").asText().equals("")) {
                    cw.visitField(ACC_PUBLIC, "noName", field.get("type").asText(), null, null).visitEnd();
                } else {
                    switch (type) {
                        case "none":
                            cw.visitField(ACC_PUBLIC, field.get("name").asText(), field.get("type").asText(), null, null).visitEnd();
                            break;
                        case "int":
                            cw.visitField(ACC_PUBLIC+ACC_FINAL+ACC_STATIC, field.get("name").asText(), field.get("type").asText(), null, Integer.valueOf(field.get("constant").asInt())).visitEnd();
                            break;
                    }
                }
            }

            createConstructor(i);
            // create functions
            JsonNode functions = c.get("functions");
            for (int j = 0; j < functions.size(); j++) {
                createMethod(functions.get(j));
            }
            cw.visitEnd();

            outputClassfile(c.get("name").asText(), cw);
        }

    }

    // write to package file
    private void outputClassfile(String className, ClassWriterF cw) {
        try {
            File dir = new File(pkg);
            File file = new File(dir, className + ".class");
            if (!dir.exists()) {
                dir.mkdirs();
            }
            FileOutputStream out = new FileOutputStream(file);
            out.write(cw.toByteArray());
            out.close();
        } catch (Exception e) {
            e.printStackTrace();
            return;
        }
    }

    private void createConstructor(int i) {
        JsonNode constructor = classes.get(i).get("constructor");
        MethodVisitor mv = cw.visitMethod(ACC_PUBLIC, "<init>", constructor.get("descriptor").asText(), null, null);
        JsonNode bytecodes = constructor.get("bytecode");
        mv.visitCode();
        emitBytecode(mv, bytecodes);
        mv.visitMaxs(0, 0);
        mv.visitEnd();
    }

    private void createMethod(JsonNode function) {
        int access = ACC_PUBLIC;
        if (function.get("name").asText().equals("main")) {
              access = access + ACC_STATIC;
        }

        // do something about accessors!
        // access, name, descriptor, signature, isInterface
        MethodVisitor mv = cw.visitMethod(access, function.get("name").asText(), function.get("descriptor").asText(), null, null);
        if (function.get("name").asText() == "toString") {
            mv.visitAnnotation("descriptor", true);
        }
        mv.visitCode();
        emitBytecode(mv, function.get("bytecode"));
        mv.visitMaxs(0, 0);
        mv.visitEnd();
    }

    private void createLabel(String name) {
        labels.putIfAbsent(name, new Label());
    }

    // make a map for faster lookup
    private void emitBytecode(MethodVisitor mv, JsonNode bytecodes) {
        for (int i = 0; i < bytecodes.size(); i++) {
            JsonNode bytecode = bytecodes.get(i);
            switch (bytecode.get("type").asText()) {
                case "trycatch":
                    Label start = new Label();
                    Label end = new Label();
                    Label handler = new Label();
                    Label endend = new Label();
                    mv.visitTryCatchBlock(start, end, handler, null);
                    mv.visitLabel(start);
                    emitBytecode(mv, bytecode.get("try"));
                    mv.visitLabel(end);
                    mv.visitJumpInsn(GOTO, endend);
                    mv.visitLabel(handler);
                    mv.visitInsn(POP);
                    emitBytecode(mv, bytecode.get("catch"));
                    mv.visitLabel(endend);
                case "arg_float":
                    switch (bytecode.get("instr").asText()) {
                        case "LDC":
                            mv.visitLdcInsn(bytecode.get("nr").asDouble());
                            break;
                    }
                    break;
                case "arg_long":
                    switch (bytecode.get("instr").asText()) {
                        case "LDC":
                            mv.visitLdcInsn(bytecode.get("nr").asLong());
                            break;
                    }
                    break;
                case "arg_int":
                    switch (bytecode.get("instr").asText()) {
                        case "ALOAD":
                            mv.visitVarInsn(ALOAD, bytecode.get("nr").asInt());
                            break;
                        case "ILOAD":
                            mv.visitVarInsn(ILOAD, bytecode.get("nr").asInt());
                            break;
                        case "ISTORE":
                            mv.visitVarInsn(ISTORE, bytecode.get("nr").asInt());
                            break;
                        case "ASTORE":
                            mv.visitVarInsn(ASTORE, bytecode.get("nr").asInt());
                            break;
                        case "LDC":
                            mv.visitLdcInsn(bytecode.get("nr").asInt());
                            break;
                        default:
                            System.out.println("Unknown arg_int: " + bytecode.get("instr").asText());
                    }
                    break;
                case "empty":
                    switch (bytecode.get("instr").asText()) {
                        case "ISUB":
                            mv.visitInsn(ISUB);
                            break;
                        case "L2D":
                            mv.visitInsn(L2D);
                            break;
                        case "L2I":
                            mv.visitInsn(L2I);
                            break;
                        case "I2L":
                            mv.visitInsn(I2L);
                            break;
                        case "D2L":
                            mv.visitInsn(D2L);
                            break;
                        case "IADD":
                            mv.visitInsn(IADD);
                            break;
                        case "RETURN":
                            mv.visitInsn(RETURN);
                            break;
                        case "IRETURN":
                            mv.visitInsn(IRETURN);
                            break;
                        case "LADD":
                            mv.visitInsn(LADD);
                            break;
                        case "LSUB":
                            mv.visitInsn(LSUB);
                            break;
                        case "LMUL":
                            mv.visitInsn(LMUL);
                            break;
                        case "LDIV":
                            mv.visitInsn(LDIV);
                            break;
                        case "LNEG":
                            mv.visitInsn(LNEG);
                            break;
                        case "DADD":
                            mv.visitInsn(DADD);
                            break;
                        case "DSUB":
                            mv.visitInsn(DSUB);
                            break;
                        case "DMUL":
                            mv.visitInsn(DMUL);
                            break;
                        case "POP2":
                            mv.visitInsn(POP2);
                            break;
                        case "ARRAYLENGTH":
                            mv.visitInsn(ARRAYLENGTH);
                            break;
                        case "DDIV":
                            mv.visitInsn(DDIV);
                            break;
                        case "DNEG":
                            mv.visitInsn(DNEG);
                            break;
                        case "LREM":
                            mv.visitInsn(LREM);
                            break;
                        case "DUP":
                            mv.visitInsn(DUP);
                            break;
                        case "ARETURN":
                            mv.visitInsn(ARETURN);
                            break;
                        case "POP":
                            mv.visitInsn(POP);
                            break;
                        case "LSHL":
                            mv.visitInsn(LSHL);
                            break;
                        case "LUSHR":
                            mv.visitInsn(LUSHR);
                            break;
                        case "LSHR":
                            mv.visitInsn(LSHR);
                            break;
                        case "LCMP":
                            mv.visitInsn(LCMP);
                            break;
                        case "DCMP":
                            mv.visitInsn(DCMPL);
                            break;
                        case "AASTORE":
                            mv.visitInsn(AASTORE);
                            break;
                        case "AALOAD":
                            mv.visitInsn(AALOAD);
                            break;
                        default:
                            System.out.println("Unknown empty: " + bytecode.get("instr").asText());
                    }
                    break;
                case "apply":
                    switch (bytecode.get("instr").asText()) {
                        case "INVOKESPECIAL":
                            mv.visitMethodInsn(INVOKESPECIAL, bytecode.get("owner").asText(), bytecode.get("name").asText(), bytecode.get("descriptor").asText(), false);
                            break;
                        case "GETSTATIC":
                            //opcode, owner, name, descriptor
                            mv.visitFieldInsn(GETSTATIC, bytecode.get("owner").asText(), bytecode.get("name").asText(), bytecode.get("descriptor").asText());
                            break;
                        case "GETFIELD":
                            String name = bytecode.get("name").asText();
                            if (name.equals("")) {
                                name = "noName";
                            }
                            //opcode, owner, name, descriptor
                            mv.visitFieldInsn(GETFIELD, bytecode.get("owner").asText(), name, bytecode.get("descriptor").asText());
                            break;
                        case "PUTFIELD":
                            name = bytecode.get("name").asText();
                            if (name.equals("")) {
                                name = "noName";
                            }
                            //opcode, owner, name, descriptor
                            mv.visitFieldInsn(PUTFIELD, bytecode.get("owner").asText(), name, bytecode.get("descriptor").asText());
                            break;
                        case "PUTSTATIC":
                            mv.visitFieldInsn(PUTSTATIC, bytecode.get("owner").asText(), bytecode.get("name").asText(), bytecode.get("descriptor").asText());
                            break;
                        case "INVOKEVIRTUAL":
                            mv.visitMethodInsn(INVOKEVIRTUAL, bytecode.get("owner").asText(), bytecode.get("name").asText(), bytecode.get("descriptor").asText(), false);
                            break;
                        case "INVOKEINTERFACE":
                            mv.visitMethodInsn(INVOKEINTERFACE, bytecode.get("owner").asText(), bytecode.get("name").asText(), bytecode.get("descriptor").asText(), true);
                            break;
                        case "INVOKESTATIC":
                            mv.visitMethodInsn(INVOKESTATIC, bytecode.get("owner").asText(), bytecode.get("name").asText(), bytecode.get("descriptor").asText(), false);
                            break;
                        default:
                            System.out.println("Unknown apply: " + bytecode.get("instr").asText());
                    }
                    break;
                case "arg_constant":
                    String constant = bytecode.get("constant").asText();
                    switch (bytecode.get("instr").asText()) {
                        case "LDC":
                            mv.visitLdcInsn(constant);
                            break;
                        case "NEW":
                            mv.visitTypeInsn(NEW, constant);
                            break;
                        case "CHECKCAST":
                            mv.visitTypeInsn(CHECKCAST, constant);
                            break;
                        case "LABEL":
                            createLabel(constant);
                            mv.visitLabel(labels.get(constant));
                            break;
                        case "IFEQ":
                            createLabel(constant);
                            mv.visitJumpInsn(IFEQ, labels.get(constant));
                            break;
                        case "IFNE":
                            createLabel(constant);
                            mv.visitJumpInsn(IFNE, labels.get(constant));
                            break;
                        case "IFLT":
                            createLabel(constant);
                            mv.visitJumpInsn(IFLT, labels.get(constant));
                            break;
                        case "IFGT":
                            createLabel(constant);
                            mv.visitJumpInsn(IFGT, labels.get(constant));
                            break;
                        case "IFLE":
                            createLabel(constant);
                            mv.visitJumpInsn(IFLE, labels.get(constant));
                            break;
                        case "IFGE":
                            createLabel(constant);
                            mv.visitJumpInsn(IFGE, labels.get(constant));
                            break;
                        case "IF_ICMPGE":
                            createLabel(constant);
                            mv.visitJumpInsn(IF_ICMPGE, labels.get(constant));
                            break;
                        case "IF_ICMPLT":
                            createLabel(constant);
                            mv.visitJumpInsn(IF_ICMPLT, labels.get(constant));
                            break;
                        case "IF_ICMPEQ":
                            createLabel(constant);
                            mv.visitJumpInsn(IF_ICMPEQ, labels.get(constant));
                            break;
                        case "IF_ICMPNE":
                            createLabel(constant);
                            mv.visitJumpInsn(IF_ICMPNE, labels.get(constant));
                            break;
                        case "GOTO":
                            createLabel(constant);
                            mv.visitJumpInsn(GOTO, labels.get(constant));
                            break;
                        case "ANEWARRAY":
                            mv.visitTypeInsn(ANEWARRAY, constant);
                            break;
                        case "INSTANCEOF":
                            mv.visitTypeInsn(INSTANCEOF, constant);
                            break;
                        default:
                            System.out.println("Unknown arg_constant: " + bytecode.get("instr").asText());
                    }
                    break;
                default:
                    System.out.println("Unknown type: " + bytecode.get("type").asText());
            }
        }
    }
}