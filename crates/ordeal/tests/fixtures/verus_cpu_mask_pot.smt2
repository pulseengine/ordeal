(set-logic QF_BV)
(declare-const cpu_id! (_ BitVec 32))
(declare-const mask! (_ BitVec 32))
(assert
 (bvult cpu_id! ((_ zero_extend 26) (_ bv32 6)))
)
(assert
 (= mask! (bvshl ((_ zero_extend 31) (_ bv1 1)) cpu_id!))
)
;; bitvector assertion not satisfied
(declare-const %%location_label%%0 Bool)
(assert
 (not (=>
   %%location_label%%0
   (or
    (or
     (or
      (or
       (or
        (or
         (or
          (or
           (or
            (or
             (or
              (or
               (or
                (or
                 (or
                  (or
                   (or
                    (or
                     (or
                      (or
                       (or
                        (or
                         (or
                          (or
                           (or
                            (or
                             (or
                              (or
                               (or
                                (or
                                 (or
                                  (= mask! ((_ zero_extend 31) (_ bv1 1)))
                                  (= mask! ((_ zero_extend 30) (_ bv2 2)))
                                 )
                                 (= mask! ((_ zero_extend 29) (_ bv4 3)))
                                )
                                (= mask! ((_ zero_extend 28) (_ bv8 4)))
                               )
                               (= mask! ((_ zero_extend 27) (_ bv16 5)))
                              )
                              (= mask! ((_ zero_extend 26) (_ bv32 6)))
                             )
                             (= mask! ((_ zero_extend 25) (_ bv64 7)))
                            )
                            (= mask! ((_ zero_extend 24) (_ bv128 8)))
                           )
                           (= mask! ((_ zero_extend 23) (_ bv256 9)))
                          )
                          (= mask! ((_ zero_extend 22) (_ bv512 10)))
                         )
                         (= mask! ((_ zero_extend 21) (_ bv1024 11)))
                        )
                        (= mask! ((_ zero_extend 20) (_ bv2048 12)))
                       )
                       (= mask! ((_ zero_extend 19) (_ bv4096 13)))
                      )
                      (= mask! ((_ zero_extend 18) (_ bv8192 14)))
                     )
                     (= mask! ((_ zero_extend 17) (_ bv16384 15)))
                    )
                    (= mask! ((_ zero_extend 16) (_ bv32768 16)))
                   )
                   (= mask! ((_ zero_extend 15) (_ bv65536 17)))
                  )
                  (= mask! ((_ zero_extend 14) (_ bv131072 18)))
                 )
                 (= mask! ((_ zero_extend 13) (_ bv262144 19)))
                )
                (= mask! ((_ zero_extend 12) (_ bv524288 20)))
               )
               (= mask! ((_ zero_extend 11) (_ bv1048576 21)))
              )
              (= mask! ((_ zero_extend 10) (_ bv2097152 22)))
             )
             (= mask! ((_ zero_extend 9) (_ bv4194304 23)))
            )
            (= mask! ((_ zero_extend 8) (_ bv8388608 24)))
           )
           (= mask! ((_ zero_extend 7) (_ bv16777216 25)))
          )
          (= mask! ((_ zero_extend 6) (_ bv33554432 26)))
         )
         (= mask! ((_ zero_extend 5) (_ bv67108864 27)))
        )
        (= mask! ((_ zero_extend 4) (_ bv134217728 28)))
       )
       (= mask! ((_ zero_extend 3) (_ bv268435456 29)))
      )
      (= mask! ((_ zero_extend 2) (_ bv536870912 30)))
     )
     (= mask! ((_ zero_extend 1) (_ bv1073741824 31)))
    )
    (= mask! (_ bv2147483648 32))
))))
(check-sat)
