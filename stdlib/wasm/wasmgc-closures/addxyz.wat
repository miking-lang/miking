;; Consider the following MExpr:
;; mexpr 
;; let f = lam x. lam y. lam z. addi (addi x y) z in 
;; f 1 2 3

;; We can unfold and closure convert this to:
;; let h = lam env. lam z. addi (addi env.x env.y) z in 
;; let g = lam env. lam y. h (env.x, y)
;; let f = lam env. lam x. h (x)

(module
    (type $clos (struct
        (field $func_pointer i32)
        (field $env anyref)
    ))

    (type $i32box (struct (field $value i32)))
    (func $box (param $x i32) (result (ref $i32box)) (struct.new $i32box (local.get $x)))
    (func $unbox (param $box (ref $i32box)) (result i32) (struct.get $i32box $value (local.get $box)))

    (type $h_env (struct (field $x (ref $i32box)) (field $y (ref $i32box))))
    (type $g_env (struct (field $x (ref $i32box))))
    (type $f_env (struct))

    (type $h_type (func (param (ref $h_env)) (param (ref $i32box)) (result (ref $i32box))))
    (type $g_type (func (param (ref $g_env)) (param (ref $i32box)) (result (ref $clos))))
    (type $f_type (func (param (ref $f_env)) (param (ref $i32box)) (result (ref $clos))))
    (type $generic_type (func (param anyref) (param anyref) (result anyref)))
    
    (func $h (param $env anyref) (param $z anyref) (result anyref)
        (local $x_val i32)
        (local $y_val i32)
        (local $z_val i32)
        (local.set $x_val (call $unbox (struct.get $h_env $x 
            (ref.cast (ref $h_env) (local.get $env)))))
        (local.set $y_val (call $unbox (struct.get $h_env $y
            (ref.cast (ref $h_env) (local.get $env)))))
        (local.set $z_val (call $unbox (ref.cast (ref $i32box) (local.get $z))))
        (call $box (i32.add 
            (i32.add 
                (local.get $x_val) 
                (local.get $y_val)) 
            (local.get $z_val)))
    )

    (func $g (param $env anyref) (param $y anyref) (result anyref)
        (local $x (ref $i32box))
        (local.set $x (struct.get $g_env $x (ref.cast (ref $g_env) (local.get $env))))
        (struct.new $clos 
            (i32.const 0) ;; function pointer to h
            (struct.new $h_env (local.get $x) (ref.cast (ref $i32box) (local.get $y)))
        )
    )

    (func $f (param $env anyref) (param $x anyref) (result anyref)
        (struct.new $clos 
            (i32.const 1) ;; function pointer to g
            (struct.new $g_env (ref.cast (ref $i32box) (local.get $x)))
        )
    )

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
                        (struct.new $clos (i32.const 2) (struct.new $f_env))
                        (call $box (i32.const 3)))
                    (call $box (i32.const 2)))
                (call $box (i32.const 1))))
        (call $unbox (ref.cast (ref $i32box) (local.get $result)))
    )
)