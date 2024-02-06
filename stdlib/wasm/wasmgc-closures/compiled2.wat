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

    (func $unbox (param $box (ref $i32box)) (result i32)
            (struct.get $i32box $value
            (local.get $box)))

    (func $sum (param $arg0 anyref) (param $arg1 anyref) (result anyref)
        (local $env (ref $sum-env))
        (local $l anyref)
            (local.set $env
            (ref.cast
                (ref $sum-env)
                (local.get $arg0)))
        (local.set $l
            (local.get $arg1))
        (select

            (call $box
                (i32.add
                    (call $unbox
                        (struct.get $IntList-IntCons $field0
                            (ref.cast
                                (ref $IntList-IntCons)
                                (local.get $l))))
                    (call $unbox
                        (call $apply
                            (struct.new $clos
                                (i32.const 0)
                                (struct.new $sum-env))
                            (struct.get $IntList-IntCons $field1
                                (ref.cast
                                    (ref $IntList-IntCons)
                                    (local.get $l)))))))
            (call $box
                (i32.const 0))
            (i32.and
                (ref.test
                    (ref $IntList-IntCons)
                    (local.get $l))
                (i32.eq
                    (i32.const 1)
                    (struct.get $IntList-IntCons $_typeid
                        (ref.cast
                            (ref $IntList-IntCons)
                            (local.get $l)))))))

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
