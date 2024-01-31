(module  
    (type $type-i32-i32 (func (param i32) (result i32)))
    (type $clos-i32-i32 (struct
        (field $func_pointer i32)
        (field $arg0 anyref)
    ))

    (type $i32box (struct (field $value i32)))

    (type $type-add (func (param (ref $i32box)) (param i32) (result i32)))
    (type $type-twice (func (param (ref $clos-i32-i32)) (param i32) (result i32)))  

    (func $addi (param $box (ref $i32box)) (param $y i32) (result i32)
        (i32.add (struct.get $i32box $value (local.get $box)) (local.get $y))
    )

    (func $twice (param $clos (ref $clos-i32-i32)) (param $x i32) (result i32)
        (call $apply (local.get $clos) (call $apply (local.get $clos) (local.get $x)))
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

    (func $apply-add (param $clos (ref $clos-i32-i32)) (param $x i32) (result i32)
        (call_indirect
            (type $type-add)  ;; Function type
            ;; (struct.new $i32box (i32.const 10))
            (ref.cast (ref $i32box) (struct.get $clos-i32-i32 $arg0 (local.get $clos)))
            (local.get $x)
            (struct.get $clos-i32-i32 $func_pointer (local.get $clos))))  

    (func $apply-twice (param $clos (ref $clos-i32-i32)) (param $x i32) (result i32)
        (call_indirect
            (type $type-twice)  ;; Function type
            (ref.cast (ref $clos-i32-i32) (struct.get $clos-i32-i32 $arg0 (local.get $clos)))
            (local.get $x)
            (struct.get $clos-i32-i32 $func_pointer (local.get $clos)))) 

    (func $apply (param $clos (ref $clos-i32-i32)) (param $arg i32) (result i32)
        (local $fp i32)
        (local $result i32)
        (local.set $fp (struct.get $clos-i32-i32 $func_pointer (local.get $clos)))
        (if (i32.eq (local.get $fp) (i32.const 0))
            (then (local.set $result (call $apply-add (local.get $clos) (local.get $arg))) )
            ;; (else (local.set $result (i32.const 666))))
            (else (local.set $result (call $apply-twice (local.get $clos) (local.get $arg)))))
        (local.get $result)
    )

    (func (export "mexpr") (result i32)
        (local $incr (ref $clos-i32-i32))
        (local $addTwo (ref $clos-i32-i32))
        (local.set $incr (call $make-addi (i32.const 111)))
        (local.set $addTwo (call $make-twice (local.get $incr)))
        (call $apply (local.get $addTwo) (i32.const 1000))
    )
)