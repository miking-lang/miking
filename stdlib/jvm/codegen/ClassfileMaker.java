package codegen;

import org.objectweb.asm.ClassWriter;
import org.objectweb.asm.MethodVisitor;
import static org.objectweb.asm.Opcodes.*;
import org.objectweb.asm.Label;
import java.io.FileOutputStream;
import java.io.File;

import java.util.*;

import javax.swing.event.CaretEvent;
import javax.swing.text.FieldView;

import com.fasterxml.jackson.databind.*;

class ClassfileMaker {
    ClassWriter cw;
    JsonNode classes;
    JsonNode interfaces;
    ClassWriter iw;
    String pkg;
    Map<String, Label> labels;

    public ClassfileMaker(JsonNode json) {
        pkg = json.get("package").asText();
        labels = new HashMap<String, Label>();

        interfaces = json.get("interfaces");
        
        for (int i = 0; i < interfaces.size(); i++) {
            iw = new ClassWriter(ClassWriter.COMPUTE_MAXS+ClassWriter.COMPUTE_FRAMES);
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
            cw = new ClassWriter(ClassWriter.COMPUTE_MAXS);
            // version, access, name, signature, superName, String[] interfaces
            cw.visit(V1_5, ACC_PUBLIC + ACC_SUPER, pkg + c.get("name").asText(), null, "java/lang/Object", interf);


            // create fields
            JsonNode fields = c.get("fields");
            for (int j = 0; j < fields.size(); j++) {
                JsonNode field = fields.get(j);
                cw.visitField(ACC_PUBLIC, field.get("name").asText(), field.get("type").asText(), null, null).visitEnd();
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
    private void outputClassfile(String className, ClassWriter cw) {
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
            return;
        }
    }

    private void createConstructor(int i) {
        JsonNode constructor = classes.get(i).get("constructor");
        MethodVisitor mv = cw.visitMethod(ACC_PUBLIC, "<init>", constructor.get("descriptor").asText(), null, null);
        JsonNode bytecodes = constructor.get("bytecode");
        emitBytecode(mv, bytecodes);
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
        emitBytecode(mv, function.get("bytecode"));
        mv.visitEnd();
    }

    private void createLabel(String name) {
        labels.putIfAbsent(name, new Label());
    }

    private void emitBytecode(MethodVisitor mv, JsonNode bytecodes) {
        mv.visitCode();
        for (int i = 0; i < bytecodes.size(); i++) {
            JsonNode bytecode = bytecodes.get(i);
            switch (bytecode.get("type").asText()) {
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
                        case "RETURN":
                            mv.visitInsn(RETURN);
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
                        case "LCMP":
                            mv.visitInsn(LCMP);
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
                            //opcode, owner, name, descriptor
                            mv.visitFieldInsn(GETFIELD, bytecode.get("owner").asText(), bytecode.get("name").asText(), bytecode.get("descriptor").asText());
                            break;
                        case "PUTFIELD":
                            mv.visitFieldInsn(PUTFIELD, bytecode.get("owner").asText(), bytecode.get("name").asText(), bytecode.get("descriptor").asText());
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
                        case "IFLT":
                            createLabel(constant);
                            mv.visitJumpInsn(IFLT, labels.get(constant));
                            break;
                        case "IF_ICMPEQ":
                            createLabel(constant);
                            mv.visitJumpInsn(IF_ICMPEQ, labels.get(constant));
                            break;
                        default:
                            System.out.println("Unknown arg_constant: " + bytecode.get("instr").asText());
                    }
                    break;
                default:
                    System.out.println("Unknown type: " + bytecode.get("type").asText());
            }
        }
        mv.visitMaxs(0, 0);
    }
}