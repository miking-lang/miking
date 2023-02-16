package codegen;

import org.objectweb.asm.ClassWriter;
import org.objectweb.asm.MethodVisitor;
import static org.objectweb.asm.Opcodes.*;
import java.io.FileOutputStream;

import javax.swing.event.CaretEvent;

import com.fasterxml.jackson.databind.*;

class ClassfileMaker {
    ClassWriter cw;
    JsonNode classes;

    public ClassfileMaker(JsonNode json) {
        classes = json.get("classes");
        
        for (int i = 0; i < classes.size(); i++) {
            cw = new ClassWriter(ClassWriter.COMPUTE_MAXS);
            // version, access, name, signature, superName, String[] interfaces
            cw.visit(V1_5, ACC_PUBLIC + ACC_SUPER, classes.get(0).get("name").asText(), null, "java/lang/Object", null);
            createConstructor(i);
            // create functions
            JsonNode functions = classes.get(i).get("functions");
            for (int j = 0; j < functions.size(); j++) {
                createMethod(functions.get(j));
            }
            cw.visitEnd();

            try {
                FileOutputStream out = new FileOutputStream(classes.get(i).get("name").asText()+".class");
                out.write(cw.toByteArray());
                out.close();
            } catch (Exception e) {
                return;
            }
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
        // do something about accessors!
        // access, name, descriptor, signature, isInterface
        MethodVisitor mv = cw.visitMethod(ACC_PUBLIC+ACC_STATIC, function.get("name").asText(), function.get("descriptor").asText(), null, null);
        emitBytecode(mv, function.get("bytecode"));
        mv.visitEnd();
    }

    private void emitBytecode(MethodVisitor mv, JsonNode bytecodes) {
        mv.visitCode();
        for (int i = 0; i < bytecodes.size(); i++) {
            JsonNode bytecode = bytecodes.get(i);
            switch (bytecode.get("instr").asText()) {
                case "ALOAD":
                    mv.visitVarInsn(ALOAD, bytecode.get("nr").asInt());
                    break;
                case "IADD":
                    mv.visitInsn(IADD);
                    break;
                case "INVOKESPECIAL": 
                    mv.visitMethodInsn(INVOKESPECIAL, bytecode.get("owner").asText(), bytecode.get("name").asText(), bytecode.get("descriptor").asText(), false);
                    break;
                case "RETURN":
                    mv.visitInsn(RETURN);
                    break;
                case "GETSTATIC":
                    //opcode, owner, name, descriptor
                    mv.visitFieldInsn(GETSTATIC, bytecode.get("owner").asText(), bytecode.get("name").asText(), bytecode.get("descriptor").asText());
                    break;
                case "LDC":
                    mv.visitLdcInsn(bytecode.get("constant").asText());
                    break;
                case "INVOKEVIRTUAL":
                    mv.visitMethodInsn(INVOKEVIRTUAL, bytecode.get("owner").asText(), bytecode.get("name").asText(), bytecode.get("descriptor").asText(), false);
                    break;
            }
        }
        mv.visitMaxs(0, 0);
    }
}