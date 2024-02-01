(module
    (type $clos (struct
        (field $func_pointer i32)
        (field $env anyref)
    ))

    (type $i32box (struct (field $value i32)))


    (type $h-env 
        (struct 
            (field $y (ref $i32box)) 
            (field $x (ref $i32box))))
    (type $g-env (struct (field $x (ref $i32box))))
    (type $f-env (struct))
    (type $empty-env (struct))


    (func $box (param $x i32) (result (ref $i32box)) (struct.new $i32box (local.get $x)))
    (func $unbox (param $box (ref $i32box)) (result i32) (struct.get $i32box $value (local.get $box)))

    (type $generic_type (func (param anyref) (param anyref) (result anyref)))
    
    (func $f (param $arg0 anyref) (param $arg1 anyref) (result anyref)
    (local $env (ref $f-env))
    (local $x (ref $i32box))
        (local.set $env
        (ref.cast
            (ref $f-env)
            (local.get $arg0)))
        (local.set $x
        (ref.cast
            (ref $i32box)
            (local.get $arg1)))
        (struct.new $clos
        (i32.const 1)
        (struct.new $g-env
            (local.get $x))))
(func $g (param $arg0 anyref) (param $arg1 anyref) (result anyref)
    (local $env (ref $g-env))
    (local $y (ref $i32box))
        (local.set $env
        (ref.cast
            (ref $g-env)
            (local.get $arg0)))
        (local.set $y
        (ref.cast
            (ref $i32box)
            (local.get $arg1)))
        (struct.new $clos
        (i32.const 0)
        (struct.new $h-env
            (local.get $y)
            (struct.get $g-env $x
                (ref.cast
                    (ref $g-env)
                    (local.get $env))))))
(func $h (param $arg0 anyref) (param $arg1 anyref) (result anyref)
    (local $env (ref $h-env))
    (local $z (ref $i32box))
        (local.set $env
        (ref.cast
            (ref $h-env)
            (local.get $arg0)))
        (local.set $z
        (ref.cast
            (ref $i32box)
            (local.get $arg1)))
        (call $box
        (i32.add
            (call $unbox
                (call $box
                    (i32.add
                        (call $unbox
                            (struct.get $h-env $x
                                (ref.cast
                                    (ref $h-env)
                                    (local.get $env))))
                        (call $unbox
                            (struct.get $h-env $y
                                (ref.cast
                                    (ref $h-env)
                                    (local.get $env)))))))
            (call $unbox
                (local.get $z)))))





    (table 10 funcref)
    (elem (i32.const 0) $h $g $f)

    (func $apply (param $c_uncast anyref) (param $env anyref) (result anyref)
        (local $cl (ref $clos))
        (local.set $cl (ref.cast (ref $clos) (local.get $c_uncast)))
        (call_indirect
            (type $generic_type)
            (struct.get $clos $env (local.get $cl))
            (local.get $env)
            (struct.get $clos $func_pointer (local.get $cl)))
    )

    (func (export "mexpr") (result i32)
     (local $result anyref)
        (local.set 
            $result
            (call $apply
                (call $apply 
                    (call $apply
                        (struct.new $clos (i32.const 2) (struct.new $f-env))
                        (call $box (i32.const 3)))
                    (call $box (i32.const 2)))
                (call $box (i32.const 1))))
        (call $unbox (ref.cast (ref $i32box) (local.get $result)))
        ;; (call $unbox
        ;;     (ref.cast (ref $i32box)

                ;; (call $apply 
                ;;     (struct.new $clos 
                ;;         (i32.const 0)
                ;;         (struct.new $h-env (call $box (i32.const 1)) (call $box (i32.const 1)))) 
                ;;     (call $box (i32.const 10)))))
    )
)