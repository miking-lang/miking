;; Consider the following MExpr:
;; mexpr 
;; let f = lam x. lam y. lam z. addi (addi x y) z in 
;; f 1 2 3

;; We can unfold and closure convert this to:
;; let h = lam env. lam z. addi (addi env.x env.y) z in 
;; let g = lam env. lam y. h (env.x, y)
;; let f = lam x. h (x)

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
    
    (func $h (param $env (ref $h_env)) (param $z (ref $i32box)) (result (ref $i32box))
        (local $x_val i32)
        (local $y_val i32)
        (local $z_val i32)
        (local.set $x_val (call $unbox (struct.get $h_env $x (local.get $env))))
        (local.set $y_val (call $unbox (struct.get $h_env $y (local.get $env))))
        (local.set $z_val (call $unbox (local.get $z)))
        (call $box (i32.add 
            (i32.add 
                (local.get $x_val) 
                (local.get $y_val)) 
            (local.get $z_val)))
    )

    (func $g (param $env (ref $g_env)) (param $y (ref $i32box)) (result (ref $clos))
        (local $x (ref $i32box))
        (local.set $x (struct.get $g_env $x (local.get $env)))
        (struct.new $clos 
            (i32.const 0) ;; function pointer to h
            (struct.new $h_env (local.get $x) (local.get $y))
        )
    )

    (func $f (param $env (ref $f_env)) (param $x (ref $i32box)) (result (ref $clos))
        (struct.new $clos 
            (i32.const 1) ;; function pointer to g
            (struct.new $g_env (local.get $x))
        )
    )

    (table 10 funcref)
    (elem (i32.const 0) $h $g $f)
 
    (func $apply_h (param $cl (ref $clos)) (param $z anyref) (result (ref $i32box))
        (call_indirect
            (type $h_type)  ;; Function type
            ;; (struct.new $i32box (i32.const 10))
            (ref.cast (ref $h_env) (struct.get $clos $env (local.get $cl)))
            (ref.cast (ref $i32box) (local.get $z))
            (struct.get $clos $func_pointer (local.get $cl)))) 

    
    (func $apply_g (param $cl (ref $clos)) (param $y anyref) (result (ref $clos))
        (call_indirect
            (type $g_type)  ;; Function type
            ;; (struct.new $i32box (i32.const 10))
            (ref.cast (ref $g_env) (struct.get $clos $env (local.get $cl)))
            (ref.cast (ref $i32box) (local.get $y))
            (struct.get $clos $func_pointer (local.get $cl))))


    ;; (func $apply-twice (param $clos (ref $clos-i32-i32)) (param $x anyref) (result (ref $i32box))
    ;;     (call_indirect
    ;;         (type $type-twice)  ;; Function type
    ;;         (ref.cast (ref $clos-i32-i32) (struct.get $clos-i32-i32 $env (local.get $clos)))
    ;;         (ref.cast (ref $i32box) (local.get $x))
    ;;         (struct.get $clos-i32-i32 $func_pointer (local.get $clos)))) 

    (func $apply (param $clos (ref $clos)) (param $env anyref) (result anyref)
        (local $fp i32)
        (local $result anyref)
        (local.set $fp (struct.get $clos $func_pointer (local.get $clos)))
        (if (i32.eq (local.get $fp) (i32.const 0))
            (then (local.set $result (call $apply_h (local.get $clos) (local.get $env))) )
            ;; (else (local.set $result (call $box (i32.const 666)))))
            (else (local.set $result (call $apply_g (local.get $clos) (local.get $env)))))
        (local.get $result)
    )




    ;; (elem (i32.const 0) $addi $twice)

   

    (func (export "mexpr") (result i32)
        (local $result (ref $i32box))
        (local.set $result (ref.cast (ref $i32box) 
            (call $apply 
            (ref.cast (ref $clos) 
                (call $apply 
                    (struct.new $clos 
                        (i32.const 1)
                        (ref.cast anyref (struct.new $g_env (call $box (i32.const 1)))))
                    (ref.cast anyref (call $box (i32.const 10)))))
                (call $box (i32.const 10)))))
        (call $unbox (local.get $result))
    )
)