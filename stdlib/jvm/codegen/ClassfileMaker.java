package codegen;

import org.objectweb.asm.ClassWriter;
import org.objectweb.asm.MethodVisitor;
import static org.objectweb.asm.Opcodes.*;
import java.io.FileOutputStream;
import java.io.File;

import javax.swing.event.CaretEvent;
import javax.swing.text.FieldView;

import com.fasterxml.jackson.databind.*;

class ClassfileMaker {
    ClassWriter cw;
    JsonNode classes;
    JsonNode interfaces;
    ClassWriter iw;
    String pkg;

    public ClassfileMaker(JsonNode json) {
        pkg = json.get("package").asText();

        interfaces = json.get("interfaces");
        
        for (int i = 0; i < interfaces.size(); i++) {
            iw = new ClassWriter(ClassWriter.COMPUTE_MAXS);
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

    private void emitBytecode(MethodVisitor mv, JsonNode bytecodes) {
        mv.visitCode();
        for (int i = 0; i < bytecodes.size(); i++) {
            JsonNode bytecode = bytecodes.get(i);
            switch (bytecode.get("type").asText()) {
                case "arg_float":
                    switch (bytecode.get("instr").asText()) { 
                        case "LDC":
                            mv.visitLdcInsn((float) bytecode.get("nr").asDouble());
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
                        case "IADD":
                            mv.visitInsn(IADD);
                            break;
                        case "ISUB":
                            mv.visitInsn(ISUB);
                            break;
                        case "IMUL":
                            mv.visitInsn(IMUL);
                            break;
                        case "IDIV":
                            mv.visitInsn(IDIV);
                            break;
                        case "INEG":
                            mv.visitInsn(INEG);
                            break;
                        case "FADD":
                            mv.visitInsn(FADD);
                            break;
                        case "FSUB":
                            mv.visitInsn(FSUB);
                            break;
                        case "FMUL":
                            mv.visitInsn(FMUL);
                            break;
                        case "FDIV":
                            mv.visitInsn(FDIV);
                            break;
                        case "FNEG":
                            mv.visitInsn(FNEG);
                            break;
                        case "IREM":
                            mv.visitInsn(IREM);
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
                    switch (bytecode.get("instr").asText()) {
                        case "LDC":
                            mv.visitLdcInsn(bytecode.get("constant").asText());
                            break;
                        case "NEW":
                            mv.visitTypeInsn(NEW, bytecode.get("constant").asText());
                            break;
                        case "CHECKCAST":
                            mv.visitTypeInsn(CHECKCAST, bytecode.get("constant").asText());
                            break;
                        default:
                            System.out.println("Unknown arg_constant");
                    }
                    break;
                default:
                    System.out.println("Unknown type: " + bytecode.get("instr").asText());
            }
        }
        mv.visitMaxs(0, 0);
    }
}