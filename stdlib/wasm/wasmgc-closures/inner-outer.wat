(module  
    (type $type-i32-i32 (func (param i32) (result i32)))
    (type $clos-i32-i32 (struct
        (field $func_pointer i32)
        (field $arg0 i32)
    ))
    (type $clos-twice-i32-i32 (struct
        (field $func_pointer i32)
        (field $arg0 (ref $clos-i32-i32))
    ))
    (type $type-i32-i32-i32 (func (param i32) (param i32) (result i32)))
    (type $type-twice (func (param (ref $clos-i32-i32)) (param i32) (result i32)))
    (type $clos-i32-i32-i32 (struct
        (field $func_pointer i32)
        (field $arg0 i32)
        (field $arg1 i32)
    ))
    (type $type-i32-clos-i32-i32 (func (param i32) (result (ref $clos-i32-i32))))

    (func $add-intrinsic (param i32) (param i32) (result i32)
        (i32.add (local.get 0) (local.get 1))
    )

    (func $twice-base (param $clos (ref $clos-i32-i32)) (param $x i32) (result i32)
        (call $apply (local.get $clos) (call $apply (local.get $clos) (local.get $x)))
    )

    (func $addi (param $x i32) (result (ref $clos-i32-i32))
        (struct.new $clos-i32-i32 (i32.const 0) (local.get $x))
    )

    (func $make-twice (param $f (ref $clos-i32-i32)) (result (ref $clos-twice-i32-i32))
        (struct.new $clos-twice-i32-i32 (i32.const 1) (local.get $f))
    )

    (table 10 funcref)

    (elem (i32.const 0) $add-intrinsic $twice-base)

    (func $exec-i32-i32 (param $clos (ref $clos-i32-i32)) (result i32)
        (call_indirect
            (type $type-i32-i32)  ;; Function type
            (struct.get $clos-i32-i32 $arg0 (local.get $clos))
            (struct.get $clos-i32-i32 $func_pointer (local.get $clos))))

    (func $apply (param $clos (ref $clos-i32-i32)) (param $x i32) (result i32)
        (call_indirect
            (type $type-i32-i32-i32)  ;; Function type
            (struct.get $clos-i32-i32 $arg0 (local.get $clos))
            (local.get $x)
            (struct.get $clos-i32-i32 $func_pointer (local.get $clos))))  

    (func $apply2 (param $clos (ref $clos-twice-i32-i32)) (param $x i32) (result i32)
        (call_indirect
            (type $type-twice)  ;; Function type
            (struct.get $clos-twice-i32-i32 $arg0 (local.get $clos))
            (local.get $x)
            (struct.get $clos-twice-i32-i32 $func_pointer (local.get $clos)))) 


    (func (export "mexpr") (result i32)
        (local $incr (ref $clos-i32-i32))
        (local $addTwo (ref $clos-twice-i32-i32))
        (local.set $incr (call $addi (i32.const 1)))
        (local.set $addTwo (call $make-twice (local.get $incr)))
        (call $apply2 (local.get $addTwo) (i32.const 98))
        ;; (i32.const 33)
        ;; (call $twice (local.get $incr) (i32.const 91))
        ;; (call $apply (local.get $incr) (i32.const 10))
        
        ;; (call $exec-i32-i32-i32 (struct.new $clos-i32-i32-i32 (i32.const 0) (i32.const 999) (i32.const 1001)))
    )
)