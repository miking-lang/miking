package codegen;

import org.objectweb.asm.ClassWriter;

public class ClassWriterF extends ClassWriter {
    
    public ClassWriterF(int flags) {
        super(flags);
    }

    @Override
    protected String getCommonSuperClass(final String type1, final String type2) {
        try {
            return super.getCommonSuperClass(type1, type2);
        } catch (TypeNotPresentException e) {
            if (type1 == type2) {
                return type1;
            } else if (type1.startsWith("pkg/") || type2.startsWith("pkg/")) {
                return "java/lang/Object";
            } else if (type1.startsWith("scala") || type2.startsWith("scala")) {
                return "java/lang/Object";
            }
            throw new RuntimeException("Unknown superclass: " + type1 + " " + type2);
        }
    }
}
