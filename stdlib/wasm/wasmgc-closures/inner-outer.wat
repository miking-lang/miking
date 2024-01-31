(module  
    (type $type-i32-i32 (func (param i32) (result i32)))
    (type $clos-i32-i32 (struct
        (field $func_pointer i32)
        (field $arg0 anyref)
    ))

    (type $i32box (struct (field $value i32)))

    (func $box (param $x i32) (result (ref $i32box))
        (struct.new $i32box (local.get $x)))

    (func $unbox (param $box (ref $i32box)) (result i32)
        (struct.get $i32box $value (local.get $box)))

    (type $type-add (func (param (ref $i32box)) (param (ref $i32box)) (result (ref $i32box))))
    (type $type-twice (func (param (ref $clos-i32-i32)) (param (ref $i32box)) (result (ref $i32box))))  

    (func $addi (param $x (ref $i32box)) (param $y (ref $i32box)) (result (ref $i32box))
        (call $box (i32.add 
            (struct.get $i32box $value (local.get $x)) 
            (struct.get $i32box $value (local.get $y))))
    )

    (func $twice (param $clos (ref $clos-i32-i32)) 
                 (param $x (ref $i32box)) 
                 (result (ref $i32box))
        (ref.cast (ref $i32box) (call $apply (local.get $clos) (call $apply (local.get $clos) (local.get $x))))
    )

    (func $make-addi (param $x i32) (result (ref $clos-i32-i32))
        (struct.new 
            $clos-i32-i32 
            (i32.const 0)
            (ref.cast anyref (struct.new $i32box (local.get $x))))
    )

    (func $make-twice (param $f (ref $clos-i32-i32)) (result (ref $clos-i32-i32))
        (struct.new $clos-i32-i32 (i32.const 1) (ref.cast anyref (local.get $f)))
    )

    (table 10 funcref)

    (elem (i32.const 0) $addi $twice)
    ;; (elem (i32.const 0) $addi $twice)

    (func $apply-add (param $clos (ref $clos-i32-i32)) (param $x anyref) (result (ref $i32box))
        (call_indirect
            (type $type-add)  ;; Function type
            ;; (struct.new $i32box (i32.const 10))
            (ref.cast (ref $i32box) (struct.get $clos-i32-i32 $arg0 (local.get $clos)))
            (ref.cast (ref $i32box) (local.get $x))
            (struct.get $clos-i32-i32 $func_pointer (local.get $clos))))  

    (func $apply-twice (param $clos (ref $clos-i32-i32)) (param $x anyref) (result (ref $i32box))
        (call_indirect
            (type $type-twice)  ;; Function type
            (ref.cast (ref $clos-i32-i32) (struct.get $clos-i32-i32 $arg0 (local.get $clos)))
            (ref.cast (ref $i32box) (local.get $x))
            (struct.get $clos-i32-i32 $func_pointer (local.get $clos)))) 

    (func $apply (param $clos (ref $clos-i32-i32)) (param $arg anyref) (result anyref)
        (local $fp i32)
        (local $result anyref)
        (local.set $fp (struct.get $clos-i32-i32 $func_pointer (local.get $clos)))
        (if (i32.eq (local.get $fp) (i32.const 0))
            (then (local.set $result (call $apply-add (local.get $clos) (local.get $arg))) )
            ;; (else (local.set $result (call $box (i32.const 666)))))
            (else (local.set $result (call $apply-twice (local.get $clos) (local.get $arg)))))
        (local.get $result)
    )

    (func (export "mexpr") (result i32)
        (local $incr (ref $clos-i32-i32))
        (local $addTwo (ref $clos-i32-i32))
        (local.set $incr (call $make-addi (i32.const 1)))
        (local.set $addTwo (call $make-twice (local.get $incr)))
        (call $unbox (ref.cast (ref $i32box) (call $apply (local.get $addTwo) (call $box (i32.const 40)))))
    )
)