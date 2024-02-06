(module
    (table 1 funcref)

    (type $clos
        (struct
            (field $func_pointer i32)
            (field $env anyref)))

    (type $i32box
        (struct
            (field $value i32)))

    (type $generic-type (func (param anyref) (param anyref) (result anyref)))

    (type $IntList-IntNil
        (struct
            (field $_typeid i32)))

    (type $IntList-IntCons
        (struct
            (field $field0 anyref)
            (field $field1 anyref)
            (field $_typeid i32)))

    (type $sum-env
        (struct))

    (func $box (param $x i32) (result (ref $i32box))
            (struct.new $i32box
            (local.get $x)))

    (func $unbox (param $box anyref) (result i32)
            (struct.get $i32box $value
            (ref.cast
                (ref $i32box)
                (local.get $box))))

    (func $sum (param $arg0 anyref) (param $arg1 anyref) (result anyref)
        (local $env (ref $sum-env))
        (local $l anyref)
        (local $x anyref)
        (local $xs anyref)
        (local $tmp1 i32)
        (local $tmp0 anyref)
            (local.set $env
            (ref.cast
                (ref $sum-env)
                (local.get $arg0)))
        (local.set $l
            (local.get $arg1))
        (if
            (ref.test
                (ref $IntList-IntCons)
                (local.get $l))
            (then
            (if
                (i32.eq
                    (i32.const 1)
                    (struct.get $IntList-IntCons $_typeid
                        (ref.cast
                            (ref $IntList-IntCons)
                            (local.get $l))))
                (then
                (local.set $tmp1
                    (i32.const 1))
                (local.set $x
                    (struct.get $IntList-IntCons $field0
                        (ref.cast
                            (ref $IntList-IntCons)
                            (local.get $l))))
                (local.set $xs
                    (struct.get $IntList-IntCons $field1
                        (ref.cast
                            (ref $IntList-IntCons)
                            (local.get $l)))))
                (else
                (local.set $tmp1
                    (i32.const 0)))))
            (else
            (local.set $tmp1
                (i32.const 0))))
        (if
            (local.get $tmp1)
            (then
            (local.set $tmp0
                (call $box
                    (i32.add
                        (call $unbox
                            (local.get $x))
                        (call $unbox
                            (call $apply
                                (struct.new $clos
                                    (i32.const 0)
                                    (struct.new $sum-env))
                                (local.get $xs)))))))
            (else
            (local.set $tmp0
                (call $box
                    (i32.const 0)))))
        (local.get $tmp0))

    (func $apply (param $cl_uncast anyref) (param $arg anyref) (result anyref)
        (local $cl (ref $clos))
            (local.set $cl
            (ref.cast
                (ref $clos)
                (local.get $cl_uncast)))
        (call_indirect
            (type $generic-type)
            (struct.get $clos $env
                (local.get $cl))
            (local.get $arg)
            (struct.get $clos $func_pointer
                (local.get $cl))))

    (func $mexpr (result i32)
        (local $result anyref)
            (local.set $result
            (call $apply
                (struct.new $clos
                    (i32.const 0)
                    (struct.new $sum-env))
                (struct.new $IntList-IntCons
                    (call $box
                        (i32.const 10))
                    (struct.new $IntList-IntCons
                        (call $box
                            (i32.const 20))
                        (struct.new $IntList-IntCons
                            (call $box
                                (i32.const 30))
                            (struct.new $IntList-IntNil
                                (i32.const 0))
                            (i32.const 1))
                        (i32.const 1))
                    (i32.const 1))))
        (call $unbox
            (ref.cast
                (ref $i32box)
                (local.get $result))))

    (elem (i32.const 0) $sum)
    (export "mexpr" (func $mexpr)))
