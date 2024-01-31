(module  
    (type $type-i32-i32 (func (param i32) (result i32)))
    (type $clos-i32-i32 (struct
        (field $func_pointer i32)
        (field $arg0 i32)
    ))

    (func $add1 (param i32) (result i32)
        (i32.add (local.get 0) (i32.const 1))
    )

    (table 10 funcref)

    (elem (i32.const 0) $add1)

    (func $exec-i32-i32 (param $clos (ref $clos-i32-i32)) (result i32)
          (call_indirect
            (type $type-i32-i32)  ;; Function type
            (struct.get $clos-i32-i32 $arg0 (local.get $clos)) ;; Arg0
            (struct.get $clos-i32-i32 $func_pointer (local.get $clos))))     

    ;; (func (export "mexpr") (result (ref $clos-i32-i32))
    (func (export "mexpr") (result i32)
        (call $exec-i32-i32 (struct.new $clos-i32-i32 (i32.const 0) (i32.const 999)))
    )
)