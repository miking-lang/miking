(module
    (type $args-array (array (mut anyref)))
    (type $clos 
        (struct 
            (field $func-pointer i32)
            (field $cur-arity i32)
            (field $max-arity i32)
            (field $args (ref $args-array))))
    
    (global $null-like anyref (struct.new $i32box (i32.const 0)))

    (type $generic-type (func (param anyref) (param anyref) (result anyref)))

    (type $i32box
        (struct
            (field $value i32)))

    (func $box (param $x i32) (result (ref $i32box))
        (struct.new $i32box
            (local.get $x)))

    (func $unbox (param $box anyref) (result i32)
            (struct.get $i32box $value
            (ref.cast
                (ref $i32box)
                (local.get $box))))

    (func $addi (param $lhs anyref) (param $rhs anyref) (result anyref)
        (call $box (i32.add 
            (call $unbox (local.get $lhs))
            (call $unbox (local.get $rhs)))))

    (table 1 funcref)
    (elem (i32.const 0) $addi)

    (func $apply (param $lhs anyref) (param $arg anyref) (result anyref)
        (local $cl (ref $clos))
        (local $new-array (ref $args-array))
        (local $result anyref)
        (local $new-clos (ref $clos))

        (local.set $cl (ref.cast (ref $clos) (local.get $lhs)))
        (local.set $new-array (array.new $args-array (global.get $null-like) (i32.const 2)))

        (array.set 
            $args-array 
            (local.get $new-array) 
            (i32.const 0)
            (array.get 
                $args-array 
                (struct.get $clos $args (local.get $cl))
                (i32.const 0)))

        (array.set 
            $args-array 
            (local.get $new-array) 
            (i32.const 1)
            (array.get 
                $args-array 
                (struct.get $clos $args (local.get $cl))
                (i32.const 1)))

        (array.set 
            $args-array 
            (local.get $new-array) 
            (struct.get $clos $cur-arity (local.get $cl))
            (local.get $arg))

        (local.set $new-clos
            (struct.new $clos
                (struct.get $clos $func-pointer (local.get $cl))
                (i32.add 
                    (struct.get $clos $cur-arity (local.get $cl)) 
                    (i32.const 1))
            (struct.get $clos $max-arity (local.get $cl))
            (local.get $new-array)))

        (if (i32.eq 
                (struct.get $clos $cur-arity (local.get $new-clos))
                (struct.get $clos $max-arity (local.get $new-clos)))
            (then 
                (local.set $result 
                    (call_indirect 
                        (type $generic-type)
                        (array.get $args-array (local.get $new-array) (i32.const 0))
                        (array.get $args-array (local.get $new-array) (i32.const 1))
                        (struct.get $clos $func-pointer (local.get $new-clos)))))
            (else (local.set $result (local.get $new-clos))))
        (local.get $result))

    (func (export "mexpr") (result i32)
        (local $cl (ref $clos))
        (local $result anyref)
        (local.set $cl 
            (struct.new $clos
                (i32.const 0)
                (i32.const 0)
                (i32.const 2)
                (array.new $args-array (global.get $null-like) (i32.const 2))))

        (local.set $result
            (call $apply
                (call $apply
                    (local.get $cl)
                    (call $box (i32.const 10)))
                (call $box (i32.const 20))))
        (call $unbox (local.get $result)))
)

