(smusni-b1-lowering-subterms
 1
 (count 32)
 (outputs-sha1 "a4efa23536735e6abcfee4dce92a57c21b5a81b3")
 (outputs
  (output
   (key "samples.md#1.1")
   (source "samples.md" 1 1)
   (rules "L1.2" "L1.3" "L1.6" "L1.1")
   (disposition no-family-head)
   (offending)
   (subterms))
  (output
   (key "samples.md#3.1")
   (source "samples.md" 3 1)
   (rules "L1.2" "L1.3" "L1.6" "L1.4")
   (disposition no-family-head)
   (offending)
   (subterms))
  (output
   (key "samples.md#4.1")
   (source "samples.md" 4 1)
   (rules "L1.2" "L1.3" "L1.5")
   (disposition no-family-head)
   (offending)
   (subterms))
  (output
   (key "samples.md#5.1")
   (source "samples.md" 5 1)
   (rules "L1.2" "L1.3" "L1.6" "L1.4")
   (disposition no-family-head)
   (offending)
   (subterms))
  (output
   (key "samples.md#16.1")
   (source "samples.md" 16 1)
   (rules "L1.2" "L1.3" "L5.9" "L1.6" "L1.1")
   (disposition no-family-head)
   (offending)
   (subterms))
  (output
   (key "samples.md#17.1")
   (source "samples.md" 17 1)
   (rules "L1.2" "L1.3" "L5.12" "L5.8" "L1.6" "L1.1")
   (disposition no-family-head)
   (offending)
   (subterms))
  (output
   (key "samples.md#17.2")
   (source "samples.md" 17 2)
   (rules "L1.2" "L1.3" "L5.12" "L5.8" "L1.6" "L1.1")
   (disposition no-family-head)
   (offending)
   (subterms))
  (output
   (key "samples.md#19.1")
   (source "samples.md" 19 1)
   (rules "L3.1" "L1.2" "L1.3" "L1.1")
   (disposition no-family-head)
   (offending)
   (subterms))
  (output
   (key "samples.md#21.1")
   (source "samples.md" 21 1)
   (rules "L3.1" "L1.2" "L1.3" "L5.9" "L1.6" "L1.1")
   (disposition no-family-head)
   (offending)
   (subterms))
  (output
   (key "samples.md#22.1")
   (source "samples.md" 22 1)
   (rules "L3.2" "L1.2" "L1.3" "L1.1")
   (disposition no-family-head)
   (offending)
   (subterms))
  (output
   (key "samples.md#23.1")
   (source "samples.md" 23 1)
   (rules "L3.3" "L1.2" "L1.3" "L1.6" "L1.1")
   (disposition no-family-head)
   (offending)
   (subterms))
  (output
   (key "samples.md#27.1")
   (source "samples.md" 27 1)
   (rules "L5.22")
   (disposition no-family-head)
   (offending)
   (subterms))
  (output
   (key "samples.md#30.1")
   (source "samples.md" 30 1)
   (rules "L3.6" "L3.5")
   (disposition no-family-head)
   (offending)
   (subterms))
  (output
   (key "samples.md#34.1")
   (source "samples.md" 34 1)
   (rules "L3.14" "L3.9" "L3.15" "L3.2" "L0.1")
   (disposition no-family-head)
   (offending)
   (subterms))
  (output
   (key "samples.md#36.1")
   (source "samples.md" 36 1)
   (rules "L1.2" "L3.4" "L0.1" "L1.3" "L1.1")
   (disposition no-family-head)
   (offending)
   (subterms))
  (output
   (key "samples.md#44.1")
   (source "samples.md" 44 1)
   (rules "L1.2" "L5.1" "L0.1" "L1.3" "L1.1")
   (disposition selected)
   (offending)
   (subterms
    (subterm
     (id "58446186c6fa7dbc")
     (path 1)
     (term
      (CloseClause
       (ActualClause
        (StateClause
         (Every
          (λ ($x :: Entity)
            (CloseClause (ActualClause (StateClause (gerku :1 $x)))))
          (λ ($x :: Entity)
            (CloseClause (ActualClause (StateClause (blabi :1 $x))))))))))
     (env ()))))
  (output
   (key "samples.md#45.1")
   (source "samples.md" 45 1)
   (rules "L3.10" "L0.1" "L5.7" "L1.3" "L1.1")
   (disposition selected)
   (offending)
   (subterms
    (subterm
     (id "e41b535bf4a823c5")
     (path 1)
     (term
      (CloseClause
       (ActualClause
        (StateClause
         (No
          (λ ($x :: Entity)
            (CloseClause (ActualClause (StateClause (prenu :1 $x)))))
          (λ ($w :: Referents Entity)
            (CloseClause
             (ActualClause
              (λ ($event :: Referents Eventuality)
                (jmaji :1 $w :Eventuality $event))))))))))
     (env ()))))
  (output
   (key "samples.md#46.1")
   (source "samples.md" 46 1)
   (rules "L5.3")
   (disposition selected)
   (offending)
   (subterms
    (subterm
     (id "a4e55c1ece4724bb")
     (path 5 1)
     (term
      (CloseClause
       (ActualClause
        (StateClause
         (Distrib
          (λ ($l :: Entity)
            (Distrib
             (λ ($r :: Entity)
               (CloseClause (ActualClause (StateClause (nelci :1 $l :2 $r)))))
             $right))
          $left)))))
     (env (($right Referents Entity) ($left Referents Entity))))))
  (output
   (key "samples.md#48.1")
   (source "samples.md" 48 1)
   (rules "L5.28" "L0.1" "L5.7" "L1.3" "L1.6" "L1.1")
   (disposition selected)
   (offending)
   (subterms
    (subterm
     (id "c28906129a38b214")
     (path 3 1)
     (term
      (CloseClause
       (ActualClause
        (StateClause
         (AtLeast
          $n
          (λ ($x :: Entity)
            (CloseClause (ActualClause (StateClause (prenu :1 $x)))))
          (λ ($w :: Referents Entity)
            (CloseClause
             (ActualClause
              (λ ($event :: Referents Eventuality)
                (Bind
                 ($ctx2 :: Referents Entity)
                 (Context)
                 (Bind
                  ($ctx3 :: Referents Entity)
                  (Context)
                  (Bind
                   ($ctx4 :: Referents Entity)
                   (Context)
                   (Bind
                    ($ctx5 :: Referents Entity)
                    (Context)
                    (klama
                     :1
                     $w
                     :2
                     $ctx2
                     :3
                     $ctx3
                     :4
                     $ctx4
                     :5
                     $ctx5
                     :Eventuality
                     $event))))))))))))))
     (env (($n . Natural))))))
  (output
   (key "samples.md#58.1")
   (source "samples.md" 58 1)
   (rules "L1.2" "L1.3" "L1.6" "L1.10")
   (disposition no-family-head)
   (offending)
   (subterms))
  (output
   (key "samples.md#59.1")
   (source "samples.md" 59 1)
   (rules "L5.11")
   (disposition no-family-head)
   (offending)
   (subterms))
  (output
   (key "samples.md#63.1")
   (source "samples.md" 63 1)
   (rules "L5.29")
   (disposition no-family-head)
   (offending)
   (subterms))
  (output
   (key "samples.md#63.2")
   (source "samples.md" 63 2)
   (rules "L5.28" "L0.1" "L5.7" "L1.3" "L1.6" "L1.1")
   (disposition selected)
   (offending)
   (subterms
    (subterm
     (id "5490abdf57992a66")
     (path 5 1)
     (term
      (CloseClause
       (ActualClause
        (StateClause
         (MoreThan
          $n
          (λ ($x :: Entity)
            (CloseClause (ActualClause (StateClause (gerku :1 $x)))))
          (λ ($w :: Referents Entity)
            (CloseClause
             (ActualClause
              (λ ($event :: Referents Eventuality)
                (Bind
                 ($ctx2 :: Referents Entity)
                 (Context)
                 (Bind
                  ($ctx3 :: Referents Entity)
                  (Context)
                  (Bind
                   ($ctx4 :: Referents Entity)
                   (Context)
                   (Bind
                    ($ctx5 :: Referents Entity)
                    (Context)
                    (klama
                     :1
                     $w
                     :2
                     $ctx2
                     :3
                     $ctx3
                     :4
                     $ctx4
                     :5
                     $ctx5
                     :Eventuality
                     $event))))))))))))))
     (env (($n . Natural) ($purpose Referents Entity))))))
  (output
   (key "samples.md#63.3")
   (source "samples.md" 63 3)
   (rules "L1.8")
   (disposition no-family-head)
   (offending)
   (subterms))
  (output
   (key "samples.md#71.1")
   (source "samples.md" 71 1)
   (rules "L5.30" "L3.1" "L1.2" "L5.1" "L0.1" "L1.3" "L1.6" "L1.1")
   (disposition selected)
   (offending)
   (subterms
    (subterm
     (id "7c491742d3d8fff2")
     (path 3 1)
     (term
      (CloseClause
       (ActualClause
        (StateClause
         (Every
          (λ ($x :: Entity)
            (CloseClause (ActualClause (StateClause (gerku :1 $x)))))
          (λ ($x :: Entity)
            (CloseClause
             (ActualClause
              (λ ($event :: Referents Eventuality)
                (Bind
                 ($ctx3 :: Referents Entity)
                 (Context)
                 (tavla :1 $x :2 $r :3 $ctx3 :Eventuality $event)))))))))))
     (env (($r Referents Entity))))))
  (output
   (key "samples.md#72.1")
   (source "samples.md" 72 1)
   (rules "L5.30" "L1.2" "L5.1" "L0.1" "L5.2" "L1.3" "L1.6" "L1.1")
   (disposition selected)
   (offending)
   (subterms
    (subterm
     (id "4268934806d322ae")
     (path 1)
     (term
      (CloseClause
       (ActualClause
        (StateClause
         (Every
          (λ ($x :: Entity)
            (CloseClause (ActualClause (StateClause (gerku :1 $x)))))
          (λ ($x :: Entity)
            (Some
             (λ ($x :: Entity)
               (CloseClause (ActualClause (StateClause (mlatu :1 $x)))))
             (λ ($w :: Referents Entity)
               (CloseClause
                (ActualClause
                 (λ ($event :: Referents Eventuality)
                   (Bind
                    ($ctx3 :: Referents Entity)
                    (Context)
                    (tavla
                     :1
                     $x
                     :2
                     $w
                     :3
                     $ctx3
                     :Eventuality
                     $event)))))))))))))
     (env ()))))
  (output
   (key "spec.md#1.1")
   (source "spec.md" 1 1)
   (rules "L1.6" "L1.1")
   (disposition no-family-head)
   (offending)
   (subterms))
  (output
   (key "spec.md#2.1")
   (source "spec.md" 2 1)
   (rules "L1.6" "L1.4")
   (disposition no-family-head)
   (offending)
   (subterms))
  (output
   (key "spec.md#4.1")
   (source "spec.md" 4 1)
   (rules "L1.4")
   (disposition no-family-head)
   (offending)
   (subterms))
  (output
   (key "spec.md#9.1")
   (source "spec.md" 9 1)
   (rules "L5.2" "L0.1" "L1.3" "L1.6" "L1.1")
   (disposition no-family-head)
   (offending)
   (subterms))
  (output
   (key "spec.md#10.1")
   (source "spec.md" 10 1)
   (rules "L5.2" "L0.1")
   (disposition no-family-head)
   (offending)
   (subterms))
  (output
   (key "spec.md#19.1")
   (source "spec.md" 19 1)
   (rules "L5.21")
   (disposition no-family-head)
   (offending)
   (subterms))))
