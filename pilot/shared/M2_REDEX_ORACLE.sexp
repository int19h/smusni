(smusni-m2-redex-oracle
 1
 (count 160)
 (cases
  (case (id "0347d6a60531d233b4926705a0d467d921d7f383")
    (status available)
    (term
     (Ask
      (Polar
       (Bind
        ($ctx2 :: (Referents Entity))
        (Context)
        ($ctx3 :: (Referents Entity))
        (Context)
        ($ctx4 :: (Referents Entity))
        (Context)
        ($ctx5 :: (Referents Entity))
        (Context)
        (CloseClause
         (λ (($actual_event :: (Referents Eventuality)))
           (∧
            ((λ (($event :: (Referents Eventuality))) (klama Speaker $ctx2 $ctx3 $ctx4 $ctx5 $event)) $actual_event)
            (fasnu $actual_event)))))))))
  (case (id "04cdfd2f45e14a4ad9d525b9aa39518337dfe160")
    (status available)
    (term
     (∧
      ((λ (($left :: (Referents Entity)) ($right :: (Referents Entity)))
         (Bind
          ($ctx3 :: (Referents Entity))
          (Context)
          (CloseClause
           (λ (($actual_event :: (Referents Eventuality)))
             (∧
              ((λ (($event :: (Referents Eventuality))) (tavla $left $right $ctx3 $event)) $actual_event)
              (fasnu $actual_event))))))
       Speaker
       Audience)
      (∧
       ((λ (($left :: (Referents Entity)) ($right :: (Referents Entity)))
          (Bind
           ($ctx3 :: (Referents Entity))
           (Context)
           (CloseClause
            (λ (($actual_event :: (Referents Eventuality)))
              (∧
               ((λ (($event :: (Referents Eventuality))) (tavla $left $right $ctx3 $event)) $actual_event)
               (fasnu $actual_event))))))
        Audience
        Speaker)
       (∧)))))
  (case (id "08b939906bc81531981e2e136544295588e28456")
    (status available)
    (term
     (Bind
      ($w :: (Referents Entity))
      (SelectExactly 3 (λ (($x :: Entity)) (gerku $x)))
      (Mention
       (Bind
        ($ctx2 :: (Referents Entity))
        (Context)
        ($ctx3 :: (Referents Entity))
        (Context)
        ($ctx4 :: (Referents Entity))
        (Context)
        (CloseClause
         (λ (($actual_event :: (Referents Eventuality)))
           (∧
            ((λ (($event :: (Referents Eventuality))) (bajra $w $ctx2 $ctx3 $ctx4 $event)) $actual_event)
            (fasnu $actual_event)))))))))
  (case (id "08f992b5f049f24666cf4ace53d35d90dea91c37")
    (status available)
    (term
     (SentenceSign
      (Bind
       ($x :: Entity)
       (Context)
       (Bind
        ($ctx2 :: (Referents Entity))
        (Context)
        ($ctx3 :: (Referents Entity))
        (Context)
        ($ctx4 :: (Referents Entity))
        (Context)
        ($ctx5 :: (Referents Entity))
        (Context)
        (CloseClause
         (λ (($actual_event :: (Referents Eventuality)))
           (∧
            ((λ (($event :: (Referents Eventuality))) (klama $x $ctx2 $ctx3 $ctx4 $ctx5 $event)) $actual_event)
            (fasnu $actual_event)))))))))
  (case (id "0aca32fd93634be168dabf02d8e7156122b58fc3")
    (status unavailable)
    (reason
     "b1-expand-no: (b1-expand-no Entity (λ (($x Entity)) (Bind (($s Scale (Context))) (gerku $x))) (λ (($w (Referents Entity))) (CloseWith (row jmaji 1 direct-event (1)) ((1 $w))))) is not in my domain"))
  (case (id "0b9143a8dcab3aa4be92bcca72f9cfccf0bf8651")
    (status available)
    (term
     (Assert
      (Bind
       ($w1 :: (Referents Entity))
       (Presuppose
        (∃ (λ (($x :: Entity)) (gerku $x)))
        (Refer
         (λ (($reference :: (Referents Entity)))
           (∧
            (∧
             (∀ (λ (($member :: Entity)) (→ (Among $member $reference) ((λ (($x :: Entity)) (gerku $x)) $member))))
             (∀
              (λ (($subreference :: (Referents Entity)))
                (→
                 (Among $subreference $reference)
                 (∃
                  (λ (($member :: Entity))
                    (∧
                     ((λ (($x :: Entity)) (gerku $x)) $member)
                     (∃
                      (λ (($common :: (Referents Entity)))
                        (∧ (Among $common $member) (Among $common $subreference)))))))))))
            (∀ (λ (($member :: Entity)) (→ ((λ (($x :: Entity)) (gerku $x)) $member) (Among $member $reference))))))))
       (∀
        (λ (($member :: Entity))
          (→
           (Among $member $w1)
           ((λ (($x :: Entity))
              (Bind
               ($w1 :: (Referents Entity))
               (SelectAtLeast 1 (λ (($x :: Entity)) (mlatu $x)))
               ((λ (($w :: (Referents Entity)))
                  (Bind
                   ($ctx3 :: (Referents Entity))
                   (Context)
                   (CloseClause
                    (λ (($actual_event :: (Referents Eventuality)))
                      (∧
                       ((λ (($event :: (Referents Eventuality))) (tavla $x $w $ctx3 $event)) $actual_event)
                       (fasnu $actual_event))))))
                $w1)))
            $member))))))))
  (case (id "0c9cfd6de375ffa1d4fff442d727306600ec85f1")
    (status unavailable)
    (reason
     "a0-expand-let: (a0-expand-let $a (Act Assertion) (Assert (CloseWith (row klama 5 direct-event (1 2 3 4 5)) ((1 Speaker)))) (Bind (($o (ActOccurrence Assertion) (Perform Host $a))) (Do (Perform AttachedDisplay (Express (Close (Happiness Speaker $o Moderate))))))) is not in my domain"))
  (case (id "0dc79107606886122b69471a7a186d8eac5a1230")
    (status available)
    (term
     (Bind
      ($left :: (Referents Entity))
      (SelectExactly 3 (λ (($x :: Entity)) (gerku $x)))
      ($right :: (Referents Entity))
      (SelectExactly 2 (λ (($x1 :: Entity)) (prenu $x1)))
      (Assert
       (∀
        (λ (($member :: Entity))
          (→
           (Among $member $left)
           ((λ (($l :: Entity))
              (∀
               (λ (($member :: Entity))
                 (→
                  (Among $member $right)
                  ((λ (($r :: Entity))
                     (CloseClause
                      (λ (($actual_event :: (Referents Eventuality)))
                        (∧ ((StateClause (nelci $l $r)) $actual_event) (fasnu $actual_event)))))
                   $member)))))
            $member))))))))
  (case (id "1089e66a065f6aff2907dbf77e625afb9dabf755")
    (status available)
    (term
     (Bind
      ($alis :: (Referents Entity))
      (Refer (λ (($x :: (Referents Entity))) (Named "alis" $x)))
      (Assert
       (Bind
        ($ctx2 :: (Referents Entity))
        (Context)
        ($ctx3 :: (Referents Entity))
        (Context)
        ($ctx4 :: (Referents Entity))
        (Context)
        ($ctx5 :: (Referents Entity))
        (Context)
        (CloseClause
         (λ (($actual_event :: (Referents Eventuality)))
           (∧
            ((λ (($event :: (Referents Eventuality))) (klama $alis $ctx2 $ctx3 $ctx4 $ctx5 $event)) $actual_event)
            (fasnu $actual_event)))))))))
  (case (id "10f71e5c385cb2118c01d8439fe7d8991a7db15a")
    (status available)
    (term
     (Bind
      ($scale :: (Referents Scale))
      (Context)
      (Bind
       ($amt :: (Referents Amount))
       (Refer
        (λ (($a :: (Referents Amount)))
          ((NiRel
            (Bind
             ($ctx2 :: (Referents Entity))
             (Context)
             ($ctx3 :: (Referents Entity))
             (Context)
             ($ctx4 :: (Referents Entity))
             (Context)
             ($ctx5 :: (Referents Entity))
             (Context)
             (CloseClause
              (λ (($actual_event :: (Referents Eventuality)))
                (∧
                 ((λ (($event :: (Referents Eventuality))) (klama Speaker $ctx2 $ctx3 $ctx4 $ctx5 $event))
                  $actual_event)
                 (fasnu $actual_event))))))
           $a
           $scale)))
       (Mention (− 1 (AmountValue $amt $scale)))))))
  (case (id "1341fba432fc31883c7f2d4446847faa032bdea4")
    (status unavailable)
    (reason
     "b1-expand-at-least: (b1-expand-at-least 1 Entity (λ (($x Entity)) (gerku $x)) (λ (($w (Referents Entity))) (Bind (($s Scale (Context))) (CloseWith (row jmaji 1 direct-event (1)) ((1 $w)))))) is not in my domain"))
  (case (id "1b5d8a8c9fc9f9c06284e64734fc8ff9e530d6f9")
    (status available)
    (term (Bind ($w :: (Referents Entity)) (SelectAtLeast 1 (λ (($x :: Entity)) (gerku $x))) (Mention $w))))
  (case (id "1daf460b64ca380a9652b69a2b4870ff4d842e2a")
    (status unavailable)
    (reason
     "b1-expand-some: (b1-expand-some Entity (λ (($x Entity)) (Bind (($s Scale (Context))) (gerku $x))) (λ (($w (Referents Entity))) (CloseWith (row jmaji 1 direct-event (1)) ((1 $w))))) is not in my domain"))
  (case (id "1f879cecd53e2fce98547b4d8ef87f2446308ebe")
    (status available)
    (term
     (Bind
      ($nuclear_klama_2 :: (Referents Entity))
      (Context)
      ($nuclear_klama_3 :: (Referents Entity))
      (Context)
      ($nuclear_klama_4 :: (Referents Entity))
      (Context)
      ($nuclear_klama_5 :: (Referents Entity))
      (Context)
      (=
       (Card
        (SetOf
         (λ (($global_member :: Entity))
           (∧
            ((λ (($restrictor_member :: Entity)) (prenu $restrictor_member)) $global_member)
            ((λ (($nuclear_member :: Entity))
               (CloseClause
                (λ (($actual_event :: (Referents Eventuality)))
                  (∧
                   ((λ (($event :: (Referents Eventuality)))
                      (klama
                       $nuclear_member
                       $nuclear_klama_2
                       $nuclear_klama_3
                       $nuclear_klama_4
                       $nuclear_klama_5
                       $event))
                    $actual_event)
                   (fasnu $actual_event)))))
             $global_member)))))
       2))))
  (case (id "24a8f6ee7b1b963841362803c17af2271ae6a6d9")
    (status available)
    (term
     (SetOf
      (λ (($z :: Entity))
        (Bind
         ($w1 :: (Referents Entity))
         (SelectAtLeast 1 (λ (($x :: Entity)) (gerku $x)))
         ((λ (($w :: (Referents Entity)))
            (CloseClause
             (λ (($actual_event :: (Referents Eventuality)))
               (∧ ((λ (($event :: (Referents Eventuality))) (jmaji $w $event)) $actual_event) (fasnu $actual_event)))))
          $w1))))))
  (case (id "25087496e92097ae61f36b808ff5f741839aa26b")
    (status unavailable)
    (reason "m2-oracle: Close has no adapter-supplied lexical row declaration"))
  (case (id "258b2f3c9ce1b2f40ce28b1d99b981a3b7eed627")
    (status unavailable)
    (reason
     "a0-expand-global-exactly: (a0-expand-global-exactly 1 Entity (λ (($x Entity)) (gerku $x)) (λ (($x Entity)) (Bind (($s Scale (Context))) (CloseWith (row jmaji 1 direct-event (1)) ((1 $x)))))) is not in my domain"))
  (case (id "274806f8603d12078502192f6527633e6c13994d")
    (status available)
    (term
     (Bind
      ($r :: (Referents Entity))
      (SelectExactly 3 (λ (($x :: Entity)) (gerku $x)))
      (Assert
       (Bind
        ($ctx3 :: (Referents Entity))
        (Context)
        (CloseClause
         (λ (($actual_event :: (Referents Eventuality)))
           (∧
            ((λ (($event :: (Referents Eventuality))) (tavla Speaker $r $ctx3 $event)) $actual_event)
            (fasnu $actual_event)))))))))
  (case (id "27f27c1038df83b40e16a919fdaf24b405d04b04")
    (status available)
    (term
     (SetOf
      (λ (($z :: Entity))
        (Bind
         ($w1 :: (Referents Entity))
         (SelectAtLeast (+ 0 1) (λ (($x :: Entity)) (gerku $x)))
         ((λ (($w :: (Referents Entity)))
            (CloseClause
             (λ (($actual_event :: (Referents Eventuality)))
               (∧ ((λ (($event :: (Referents Eventuality))) (jmaji $w $event)) $actual_event) (fasnu $actual_event)))))
          $w1))))))
  (case (id "29cc86f6cefefcc0e82f7cc9606345c99e91b446")
    (status unavailable)
    (reason
     "b1-expand-at-least: no clauses matched for (b1-expand-at-least $n Entity (λ (($x Entity)) (prenu $x)) (λ (($w (Referents Entity))) (CloseWith (row klama 5 direct-event (1 2 3 4 5)) ((1 $w)))))"))
  (case (id "2a7470be1e19c3e1181aa00354f7d2f741d424e0")
    (status available)
    (term
     (Bind
      ($w1 :: (Referents Entity))
      (SelectAtLeast 1 (λ (($x :: Entity)) (gerku $x)))
      ((λ (($w :: (Referents Entity)))
         (CloseClause
          (λ (($actual_event :: (Referents Eventuality)))
            (∧ ((λ (($event :: (Referents Eventuality))) (jmaji $w $event)) $actual_event) (fasnu $actual_event)))))
       $w1))))
  (case (id "2aef1b5ba045c6dddd31e5b6c700ea6ba5769506")
    (status unavailable)
    (reason
     "b1-expand-at-most: (b1-expand-at-most 1 Entity (λ (($x Entity)) (gerku $x)) (λ (($w (Referents Entity))) (Bind (($s Scale (Context))) (CloseWith (row jmaji 1 direct-event (1)) ((1 $w)))))) is not in my domain"))
  (case (id "2b5c18cc087f6f317b301f14f4f395bfc2ca10bd")
    (status available)
    (term
     (Bind
      ($restrictor_klama_2 :: (Referents Entity))
      (Context)
      ($restrictor_klama_3 :: (Referents Entity))
      (Context)
      ($restrictor_klama_4 :: (Referents Entity))
      (Context)
      ($restrictor_klama_5 :: (Referents Entity))
      (Context)
      ($nuclear_tavla_3 :: (Referents Entity))
      (Context)
      (Assert
       (=
        (Card
         (SetOf
          (λ (($global_member :: Entity))
            (∧
             ((λ (($restrictor_member :: Entity))
                (CloseClause
                 (λ (($actual_event :: (Referents Eventuality)))
                   (∧
                    ((λ (($event :: (Referents Eventuality)))
                       (klama
                        $restrictor_member
                        $restrictor_klama_2
                        $restrictor_klama_3
                        $restrictor_klama_4
                        $restrictor_klama_5
                        $event))
                     $actual_event)
                    (fasnu $actual_event)))))
              $global_member)
             ((λ (($nuclear_member :: Entity))
                (CloseClause
                 (λ (($actual_event :: (Referents Eventuality)))
                   (∧
                    ((λ (($event :: (Referents Eventuality))) (tavla $nuclear_member Speaker $nuclear_tavla_3 $event))
                     $actual_event)
                    (fasnu $actual_event)))))
              $global_member)))))
        3)))))
  (case (id "2bbd7ecacd72e5bf39fddcbd8685bbb0c8a298e1")
    (status available)
    (term
     (Bind
      ($r :: (Referents Entity))
      (Refer (λ (($unit :: (Referents Entity))) (gerku $unit)))
      (Assert
       (Bind
        ($ctx3 :: (Referents Entity))
        (Context)
        (CloseClause
         (λ (($actual_event :: (Referents Eventuality)))
           (∧
            ((λ (($event :: (Referents Eventuality))) (tavla Speaker $r $ctx3 $event)) $actual_event)
            (fasnu $actual_event)))))))))
  (case (id "2dfd6a966b56f57fcae90ce8b9fc26926509c8cb")
    (status available)
    (term
     (Bind
      ($r :: (Referents Entity))
      (Refer (λ (($unit :: (Referents Entity))) (gerku $unit)))
      (Bind
       ($r1 :: (Referents Entity))
       (Refer (λ (($named :: (Referents Entity))) (Named "alis" $named)))
       (Assert
        (Bind
         ($ctx3 :: (Referents Entity))
         (Context)
         (CloseClause
          (λ (($actual_event :: (Referents Eventuality)))
            (∧
             ((λ (($event :: (Referents Eventuality))) (tavla $r $r1 $ctx3 $event)) $actual_event)
             (fasnu $actual_event))))))))))
  (case (id "2fcf22efb7f6212bf8ca744449fafda776c6f1c5")
    (status available)
    (term
     (Assert
      (¬
       (Bind
        ($w1 :: (Referents Entity))
        (SelectAtLeast 1 (λ (($x :: Entity)) (mlatu $x)))
        ((λ (($w :: (Referents Entity)))
           (CloseClause
            (λ (($actual_event :: (Referents Eventuality)))
              (∧ ((StateClause (blabi $w)) $actual_event) (fasnu $actual_event)))))
         $w1))))))
  (case (id "302aef64343959ab2259e4b2226ebbda2a9f188c")
    (status available)
    (term
     (Bind
      ($cats :: (Referents Entity))
      (Refer (λ (($x :: (Referents Entity))) (mlatu $x)))
      (Assert
       (Bind
        ($w :: (Referents Entity))
        (Presuppose
         (∃ (λ (($x :: Entity)) (gerku $x)))
         (Refer
          (λ (($reference :: (Referents Entity)))
            (∧
             (∧
              (∀ (λ (($member :: Entity)) (→ (Among $member $reference) ((λ (($x :: Entity)) (gerku $x)) $member))))
              (∀
               (λ (($subreference :: (Referents Entity)))
                 (→
                  (Among $subreference $reference)
                  (∃
                   (λ (($member :: Entity))
                     (∧
                      ((λ (($x :: Entity)) (gerku $x)) $member)
                      (∃
                       (λ (($common :: (Referents Entity)))
                         (∧ (Among $common $member) (Among $common $subreference)))))))))))
             (∀ (λ (($member :: Entity)) (→ ((λ (($x :: Entity)) (gerku $x)) $member) (Among $member $reference))))))))
        (∀
         (λ (($member :: Entity))
           (→
            (Among $member $w)
            ((λ (($dog :: Entity))
               (Bind
                ($ctx3 :: (Referents Entity))
                (Context)
                (CloseClause
                 (λ (($actual_event :: (Referents Eventuality)))
                   (∧
                    ((λ (($event :: (Referents Eventuality))) (tavla $dog $cats $ctx3 $event)) $actual_event)
                    (fasnu $actual_event))))))
             $member)))))))))
  (case (id "31a52745397b69a3ab4672c18fa2d64ea75cc32a")
    (status available)
    (term
     (SetOf
      (λ (($z :: Entity))
        (¬
         (Bind
          ($w1 :: (Referents Entity))
          (SelectAtLeast 1 (λ (($x :: Entity)) (gerku $x)))
          ((λ (($w :: (Referents Entity)))
             (CloseClause
              (λ (($actual_event :: (Referents Eventuality)))
                (∧ ((λ (($event :: (Referents Eventuality))) (jmaji $w $event)) $actual_event) (fasnu $actual_event)))))
           $w1)))))))
  (case (id "33adac16a15100bdd23e72514dc4a78a96e70a6b")
    (status unavailable)
    (reason
     "a0-expand-let: (a0-expand-let $a (Act Assertion) (Assert (CloseWith (row klama 5 direct-event (1 2 3 4 5)) ((1 Audience)))) (Bind (($o (ActOccurrence Assertion) (Perform Host $a))) (Do (Perform AttachedDisplay (Express (Close (Unhappiness Speaker $o Intense))))))) is not in my domain"))
  (case (id "37da0499ed432c8b54b6d072a4b1c3852e9ad2df")
    (status available)
    (term
     (Bind
      ($w :: (Referents Entity))
      (SelectExactly 3 (λ (($x :: Entity)) (gerku $x)))
      (Assert
       (Bind
        ($ctx3 :: (Referents Entity))
        (Context)
        (CloseClause
         (λ (($actual_event :: (Referents Eventuality)))
           (∧
            ((λ (($event :: (Referents Eventuality))) (tavla Speaker $w $ctx3 $event)) $actual_event)
            (fasnu $actual_event)))))))))
  (case (id "3948dd78d5112f473847359d17f681269520ce9f")
    (status available)
    (term
     (Mention
      (Bind
       ($ctx2 :: (Referents Entity))
       (Context)
       ($ctx3 :: (Referents Entity))
       (Context)
       ($ctx4 :: (Referents Entity))
       (Context)
       ($ctx5 :: (Referents Entity))
       (Context)
       (CloseClause
        (λ (($actual_event :: (Referents Eventuality)))
          (∧
           ((λ (($event :: (Referents Eventuality))) (klama Speaker $ctx2 $ctx3 $ctx4 $ctx5 $event)) $actual_event)
           (fasnu $actual_event))))))))
  (case (id "3956e1cb70c49637158cd4a7407ac5ccf982c17d")
    (status available)
    (term
     (Bind
      ($r :: (Referents Entity))
      (Refer (λ (($unit :: (Referents Entity))) (mlatu $unit)))
      (Assert
       (CloseClause
        (λ (($actual_event :: (Referents Eventuality)))
          (∧ ((StateClause (blabi $r)) $actual_event) (fasnu $actual_event))))))))
  (case (id "3adb0bedbd092a0ff9e28b5abeb9d81c14d69fb7")
    (status available)
    (term
     (Bind
      ($w :: (Referents Entity))
      (SelectExactly 3 (λ (($x :: Entity)) (gerku $x)))
      (Assert
       (Bind
        ($ctx3 :: (Referents Entity))
        (Context)
        (CloseClause
         (λ (($actual_event :: (Referents Eventuality)))
           (∧
            ((λ (($event :: (Referents Eventuality))) (tavla $w Speaker $ctx3 $event)) $actual_event)
            (fasnu $actual_event)))))))))
  (case (id "4042ee2afc837aa8bea2a718993dd4ed719ad42d")
    (status unavailable)
    (reason "m2-oracle: Close has no adapter-supplied lexical row declaration"))
  (case (id "411ad460c5065d3e54df4217a226516cb9b7e4ea")
    (status unavailable)
    (reason
     "b1-expand-some: (b1-expand-some Entity (λ (($x Entity)) (gerku $x)) (λ (($w (Referents Entity))) (Bind (($s Scale (Context))) (CloseWith (row jmaji 1 direct-event (1)) ((1 $w)))))) is not in my domain"))
  (case (id "414f10bf35ddfae2fb13794f4f47e52537896503")
    (status unavailable)
    (reason
     "b1-expand-select-some: (b1-expand-select-some Entity (λ (($x Entity)) (Bind (($s Scale (Context))) (gerku $x)))) is not in my domain"))
  (case (id "425860a14d288938ee20bc473c86d3a5ce7f287b")
    (status unavailable)
    (reason
     "b1-expand-every: (b1-expand-every Entity (λ (($x Entity)) (Bind (($s Scale (Context))) (gerku $x))) (λ (($x Entity)) (CloseWith (row jmaji 1 direct-event (1)) ((1 $x))))) is not in my domain"))
  (case (id "428f277a9ec2c492ede935d0c890b996747f1a48")
    (status available)
    (term
     (Assert
      (Bind
       ($w1 :: (Referents Entity))
       (Presuppose
        (∃ (λ (($x :: Entity)) (gerku $x)))
        (Refer
         (λ (($reference :: (Referents Entity)))
           (∧
            (∧
             (∀ (λ (($member :: Entity)) (→ (Among $member $reference) ((λ (($x :: Entity)) (gerku $x)) $member))))
             (∀
              (λ (($subreference :: (Referents Entity)))
                (→
                 (Among $subreference $reference)
                 (∃
                  (λ (($member :: Entity))
                    (∧
                     ((λ (($x :: Entity)) (gerku $x)) $member)
                     (∃
                      (λ (($common :: (Referents Entity)))
                        (∧ (Among $common $member) (Among $common $subreference)))))))))))
            (∀ (λ (($member :: Entity)) (→ ((λ (($x :: Entity)) (gerku $x)) $member) (Among $member $reference))))))))
       (∀
        (λ (($member :: Entity))
          (→
           (Among $member $w1)
           ((λ (($dog :: Entity))
              (Bind
               ($w1 :: (Referents Entity))
               (SelectAtLeast 1 (λ (($y :: Entity)) (mlatu $y)))
               ((λ (($w :: (Referents Entity)))
                  (Bind
                   ($ctx3 :: (Referents Entity))
                   (Context)
                   (CloseClause
                    (λ (($actual_event :: (Referents Eventuality)))
                      (∧
                       ((λ (($event :: (Referents Eventuality))) (tavla $dog $w $ctx3 $event)) $actual_event)
                       (fasnu $actual_event))))))
                $w1)))
            $member))))))))
  (case (id "42c5da2578ee0adc173a7789faa03e92164665f5")
    (status available)
    (term
     (λ (($p :: (Fn (Eventuality) Content)) ($c :: ClauseContent))
       (Bind ($w :: (Referents Eventuality)) (SelectExactly 1 $p) ($c $w)))))
  (case (id "433ec3111f68075021ba6c7dfe06b7b0621e2e0f")
    (status unavailable)
    (reason
     "b1-expand-at-least: no clauses matched for (b1-expand-at-least $n Entity (λ (($x Entity)) (prenu $x)) (λ (($w (Referents Entity))) (CloseWith (row klama 5 direct-event (1 2 3 4 5)) ((1 $w)))))"))
  (case (id "44e5b78b641625649b30470a6137d2e0f0c9f199")
    (status available)
    (term
     (λ (($e :: (Referents Eventuality)))
       (Bind
        ($ctx2 :: (Referents Entity))
        (Context)
        ($ctx3 :: (Referents Entity))
        (Context)
        ($ctx4 :: (Referents Entity))
        (Context)
        ($ctx5 :: (Referents Entity))
        (Context)
        (CloseClause
         (λ (($clause_event :: (Referents Eventuality)))
           (∧
            (∧ (Among $clause_event $e) (Among $e $clause_event))
            ((λ (($actual_event :: (Referents Eventuality)))
               (∧
                ((λ (($lexical_event :: (Referents Eventuality)))
                   (klama Speaker $ctx2 $ctx3 $ctx4 $ctx5 $lexical_event))
                 $actual_event)
                (fasnu $actual_event)))
             $e))))))))
  (case (id "4609d82730c3a0bb8c83f2db338169bafd034c35")
    (status unavailable)
    (reason
     "b1-expand-at-least: no clauses matched for (b1-expand-at-least $n Entity (λ (($x Entity)) (gerku $x)) (λ (($w (Referents Entity))) (CloseWith (row tavla 3 direct-event (1 2 3)) ((1 Speaker) (2 $w)))))"))
  (case (id "4852eeac9e86db4cb6d6d4a19469f720a7962e82")
    (status available)
    (term
     (Assert
      (Bind
       ($w :: (Referents Entity))
       (Presuppose
        (∃ (λ (($x :: Entity)) (gerku $x)))
        (Refer
         (λ (($reference :: (Referents Entity)))
           (∧
            (∧
             (∀ (λ (($member :: Entity)) (→ (Among $member $reference) ((λ (($x :: Entity)) (gerku $x)) $member))))
             (∀
              (λ (($subreference :: (Referents Entity)))
                (→
                 (Among $subreference $reference)
                 (∃
                  (λ (($member :: Entity))
                    (∧
                     ((λ (($x :: Entity)) (gerku $x)) $member)
                     (∃
                      (λ (($common :: (Referents Entity)))
                        (∧ (Among $common $member) (Among $common $subreference)))))))))))
            (∀ (λ (($member :: Entity)) (→ ((λ (($x :: Entity)) (gerku $x)) $member) (Among $member $reference))))))))
       (∀
        (λ (($member :: Entity))
          (→
           (Among $member $w)
           ((λ (($x :: Entity))
              (CloseClause
               (λ (($actual_event :: (Referents Eventuality)))
                 (∧ ((StateClause (blabi $x)) $actual_event) (fasnu $actual_event)))))
            $member))))))))
  (case (id "485f696c95709bf7fafedf22976a8763d63f5496")
    (status available)
    (term
     (SetOf
      (λ (($z :: Entity))
        (¬
         (Bind
          ($w1 :: (Referents Entity))
          (SelectAtLeast 1 (λ (($x :: Entity)) (gerku $x)))
          ((λ (($w :: (Referents Entity)))
             (CloseClause
              (λ (($actual_event :: (Referents Eventuality)))
                (∧ ((λ (($event :: (Referents Eventuality))) (jmaji $w $event)) $actual_event) (fasnu $actual_event)))))
           $w1)))))))
  (case (id "4955a8c68f8935068ee2677cd187fc98421260f7")
    (status available)
    (term
     (SetOf
      (λ (($z :: Entity))
        (=
         (Card
          (SetOf
           (λ (($global_member :: Entity))
             (∧
              ((λ (($x :: Entity)) (gerku $x)) $global_member)
              ((λ (($x :: Entity))
                 (CloseClause
                  (λ (($actual_event :: (Referents Eventuality)))
                    (∧
                     ((λ (($event :: (Referents Eventuality))) (jmaji $x $event)) $actual_event)
                     (fasnu $actual_event)))))
               $global_member)))))
         1)))))
  (case (id "4cc6a45509151b5a0827ca4741f05c3e9e3afb8c")
    (status available)
    (term
     (Bind
      ($r :: (Referents Entity))
      (Refer (λ (($unit :: (Referents Entity))) (gerku $unit)))
      (Bind
       ($ctx3 :: (Referents Entity))
       (Context)
       (CloseClause
        (λ (($actual_event :: (Referents Eventuality)))
          (∧
           ((λ (($event :: (Referents Eventuality))) (tavla Speaker $r $ctx3 $event)) $actual_event)
           (fasnu $actual_event))))))))
  (case (id "4d4ad03ba86cacd6bea93987224d45d7ee5e94bc")
    (status available)
    (term
     (Bind
      ($w1 :: (Referents Entity))
      (SelectAtLeast 1 (λ (($x :: Entity)) (gerku $x)))
      ((λ (($w :: (Referents Entity)))
         (Bind
          ($ctx3 :: (Referents Entity))
          (Context)
          (CloseClause
           (λ (($actual_event :: (Referents Eventuality)))
             (∧
              ((λ (($event :: (Referents Eventuality))) (tavla Speaker $w $ctx3 $event)) $actual_event)
              (fasnu $actual_event))))))
       $w1))))
  (case (id "4dac43977fdeb1253b10b424e67c05ad70fea1f2")
    (status available)
    (term
     (Bind
      ($r :: (Referents Entity))
      (Refer (λ (($unit :: (Referents Entity))) (gerku $unit)))
      (Mention
       (Bind
        ($ctx3 :: (Referents Entity))
        (Context)
        (CloseClause
         (λ (($actual_event :: (Referents Eventuality)))
           (∧
            ((λ (($event :: (Referents Eventuality))) (tavla Speaker $r $ctx3 $event)) $actual_event)
            (fasnu $actual_event)))))))))
  (case (id "4e062973565a461bfbff8b1c1e2b311b9849f16b")
    (status available)
    (term
     (Assert
      (Bind
       ($ctx2 :: (Referents Entity))
       (Context)
       ($ctx3 :: (Referents Entity))
       (Context)
       (CloseClause
        (λ (($actual_event :: (Referents Eventuality)))
          (∧
           ((λ (($event :: (Referents Eventuality))) (tavla Speaker $ctx2 $ctx3 $event)) $actual_event)
           (fasnu $actual_event))))))))
  (case (id "4e4c65ee9d06e77cf05541003764e803eb2f029a")
    (status available)
    (term
     (Bind
      ($ep :: (Referents Epistemology))
      (Context)
      (Bind
       ($tv :: (Referents TruthValue))
       (Refer
        (λ (($v :: (Referents TruthValue)))
          ((JeiRel
            (Bind
             ($ctx2 :: (Referents Entity))
             (Context)
             ($ctx3 :: (Referents Entity))
             (Context)
             ($ctx4 :: (Referents Entity))
             (Context)
             ($ctx5 :: (Referents Entity))
             (Context)
             (CloseClause
              (λ (($actual_event :: (Referents Eventuality)))
                (∧
                 ((λ (($event :: (Referents Eventuality))) (klama Speaker $ctx2 $ctx3 $ctx4 $ctx5 $event))
                  $actual_event)
                 (fasnu $actual_event))))))
           $v
           $ep)))
       (Mention $tv)))))
  (case (id "4f89bfd19bf3d029272554a38f23f8f00d4c05fe")
    (status available)
    (term
     (Bind
      ($r :: (Referents Entity))
      (Refer (λ (($unit1 :: (Referents Entity))) (mlatu $unit1)))
      (Bind
       ($r1 :: (Referents Entity))
       (Refer (λ (($unit :: (Referents Entity))) (gerku $unit)))
       (Assert
        (Bind
         ($ctx2 :: (Referents Entity))
         (Context)
         ($ctx4 :: (Referents Entity))
         (Context)
         ($ctx5 :: (Referents Entity))
         (Context)
         (CloseClause
          (λ (($actual_event :: (Referents Eventuality)))
            (∧
             ((λ (($event :: (Referents Eventuality))) (klama $r1 $ctx2 $r $ctx4 $ctx5 $event)) $actual_event)
             (fasnu $actual_event))))))))))
  (case (id "5033153a5c5b68c485fe108ee8c910f18dd71434")
    (status available)
    (term
     (Bind
      ($r :: (Referents Entity))
      (Refer (λ (($unit1 :: (Referents Entity))) (gerku $unit1)))
      (Bind
       ($r1 :: (Referents Entity))
       (Refer (λ (($unit :: (Referents Entity))) (mlatu $unit)))
       (Assert
        (Bind
         ($ctx3 :: (Referents Entity))
         (Context)
         (CloseClause
          (λ (($actual_event :: (Referents Eventuality)))
            (∧
             ((λ (($event :: (Referents Eventuality))) (tavla $r1 $r $ctx3 $event)) $actual_event)
             (fasnu $actual_event))))))))))
  (case (id "50ef8b629c53200c229526eff8a75f8fba6b259b")
    (status available)
    (term
     (Bind
      ($r :: (Referents Entity))
      (Refer (λ (($unit :: (Referents Entity))) (gerku $unit)))
      (Assert
       (Bind
        ($ctx3 :: (Referents Entity))
        (Context)
        (CloseClause
         (λ (($actual_event :: (Referents Eventuality)))
           (∧
            ((λ (($event :: (Referents Eventuality))) (tavla $r Speaker $ctx3 $event)) $actual_event)
            (fasnu $actual_event)))))))))
  (case (id "519c65d3104d364d4363ff8b27eecdec8abe7b27")
    (status available)
    (term
     (Assert
      (Bind
       ($ctx2 :: (Referents Entity))
       (Context)
       ($ctx3 :: (Referents Entity))
       (Context)
       ($ctx4 :: (Referents Entity))
       (Context)
       ($ctx5 :: (Referents Entity))
       (Context)
       (CloseClause
        (λ (($actual_event :: (Referents Eventuality)))
          (∧
           ((λ (($event :: (Referents Eventuality))) (klama Speaker $ctx2 $ctx3 $ctx4 $ctx5 $event)) $actual_event)
           (fasnu $actual_event))))))))
  (case (id "536aa8f5d8a23f0b5e51bf8b6b43a218c4634bcb")
    (status unavailable)
    (reason
     "a0-expand-global-exactly: (a0-expand-global-exactly 1 Entity (λ (($x Entity)) (Bind (($s Scale (Context))) (gerku $x))) (λ (($x Entity)) (CloseWith (row jmaji 1 direct-event (1)) ((1 $x))))) is not in my domain"))
  (case (id "53c6842442de071df126728dfc8a835ce2091e9b")
    (status available)
    (term
     (Bind
      ($dogs :: (Referents Entity))
      (SelectExactly 3 (λ (($x :: Entity)) (gerku $x)))
      ($people :: (Referents Entity))
      (SelectExactly 2 (λ (($x :: Entity)) (prenu $x)))
      (Assert
       (∀
        (λ (($member :: Entity))
          (→
           (Among $member $dogs)
           ((λ (($d :: Entity))
              (∀
               (λ (($member :: Entity))
                 (→
                  (Among $member $people)
                  ((λ (($p :: Entity))
                     (CloseClause
                      (λ (($actual_event :: (Referents Eventuality)))
                        (∧ ((StateClause (nelci $d $p)) $actual_event) (fasnu $actual_event)))))
                   $member)))))
            $member))))))))
  (case (id "58c16dbd8c5ab4d9d247b7053a082b392b277d90")
    (status unavailable)
    (reason
     "b1-expand-no: (b1-expand-no Entity (λ (($x Entity)) (gerku $x)) (λ (($w (Referents Entity))) (Bind (($s Scale (Context))) (CloseWith (row jmaji 1 direct-event (1)) ((1 $w)))))) is not in my domain"))
  (case (id "5adee1115a50ccc807e02297198c6d2c11bb1ea9")
    (status available)
    (term
     (Assert
      (Bind
       ($w1 :: (Referents Entity))
       (SelectAtLeast 1 (λ (($x :: Entity)) (gerku $x)))
       ((λ (($w :: (Referents Entity)))
          (Bind
           ($ctx3 :: (Referents Entity))
           (Context)
           (CloseClause
            (λ (($actual_event :: (Referents Eventuality)))
              (∧
               ((λ (($event :: (Referents Eventuality))) (tavla $w Speaker $ctx3 $event)) $actual_event)
               (fasnu $actual_event))))))
        $w1)))))
  (case (id "5b327dd7decfabf290e971fdee6123a55d5c4d26")
    (status available)
    (term
     (Assert
      (CloseClause
       (λ (($actual_event :: (Referents Eventuality)))
         (∧
          ((λ (($event :: (Referents Eventuality))) (jmaji (Combine Speaker Audience) $event)) $actual_event)
          (fasnu $actual_event)))))))
  (case (id "5ce3bc7019740c791f9acdfc644d21e92d62dcb7")
    (status unavailable)
    (reason
     "a0-expand-close: (a0-expand-close (row valsi 2 holding-state (1 2)) ((1 (WordSign klama)))) is not in my domain"))
  (case (id "5f5b053a4dcccf2858daa126fd3d854e0e78d516")
    (status available)
    (term
     (∧
      ((λ (($s :: (Referents Entity)) ($l :: (Referents Entity)))
         (Bind
          ($ctx3 :: (Referents Entity))
          (Context)
          (CloseClause
           (λ (($actual_event :: (Referents Eventuality)))
             (∧
              ((λ (($event :: (Referents Eventuality))) (tavla $s $l $ctx3 $event)) $actual_event)
              (fasnu $actual_event))))))
       Speaker
       Audience)
      (∧
       ((λ (($s :: (Referents Entity)) ($l :: (Referents Entity)))
          (Bind
           ($ctx3 :: (Referents Entity))
           (Context)
           (CloseClause
            (λ (($actual_event :: (Referents Eventuality)))
              (∧
               ((λ (($event :: (Referents Eventuality))) (tavla $s $l $ctx3 $event)) $actual_event)
               (fasnu $actual_event))))))
        Audience
        Speaker)
       (∧)))))
  (case (id "5fb2cbaf51ee51ea8e04140f1410110e6f30ccbf")
    (status unavailable)
    (reason "m2-oracle: Close has no adapter-supplied lexical row declaration"))
  (case (id "5feeebff2d1f37decc454689cbde025cfd011b4a")
    (status available)
    (term
     (Assert
      (Bind
       ($w :: (Referents Entity))
       (Presuppose
        (∃ (λ (($x :: Entity)) (gerku $x)))
        (Refer
         (λ (($reference :: (Referents Entity)))
           (∧
            (∧
             (∀ (λ (($member :: Entity)) (→ (Among $member $reference) ((λ (($x :: Entity)) (gerku $x)) $member))))
             (∀
              (λ (($subreference :: (Referents Entity)))
                (→
                 (Among $subreference $reference)
                 (∃
                  (λ (($member :: Entity))
                    (∧
                     ((λ (($x :: Entity)) (gerku $x)) $member)
                     (∃
                      (λ (($common :: (Referents Entity)))
                        (∧ (Among $common $member) (Among $common $subreference)))))))))))
            (∀ (λ (($member :: Entity)) (→ ((λ (($x :: Entity)) (gerku $x)) $member) (Among $member $reference))))))))
       (∀
        (λ (($member :: Entity))
          (→
           (Among $member $w)
           ((λ (($x :: Entity))
              (Bind
               ($nuclear_tavla_3 :: (Referents Entity))
               (Context)
               (=
                (Card
                 (SetOf
                  (λ (($global_member :: Entity))
                    (∧
                     ((λ (($restrictor_member :: Entity)) (mlatu $restrictor_member)) $global_member)
                     ((λ (($nuclear_member :: Entity))
                        (CloseClause
                         (λ (($actual_event :: (Referents Eventuality)))
                           (∧
                            ((λ (($event :: (Referents Eventuality)))
                               (tavla $x $nuclear_member $nuclear_tavla_3 $event))
                             $actual_event)
                            (fasnu $actual_event)))))
                      $global_member)))))
                3)))
            $member))))))))
  (case (id "60e32117d888221df45163e11f73a0509649fe93")
    (status available)
    (term
     (Mention
      (Bind
       ($w1 :: (Referents Entity))
       (SelectAtLeast 1 (λ (($x :: Entity)) (gerku $x)))
       ((λ (($w :: (Referents Entity)))
          (Bind
           ($ctx3 :: (Referents Entity))
           (Context)
           (CloseClause
            (λ (($actual_event :: (Referents Eventuality)))
              (∧
               ((λ (($event :: (Referents Eventuality))) (tavla Speaker $w $ctx3 $event)) $actual_event)
               (fasnu $actual_event))))))
        $w1)))))
  (case (id "622e4a564152b3e60db8afdd669d462b46663afe")
    (status available)
    (term
     (Bind
      ($r :: (Referents Entity))
      (Refer (λ (($unit :: (Referents Entity))) (mlatu $unit)))
      (Assert
       (Bind
        ($w :: (Referents Entity))
        (Presuppose
         (∃ (λ (($x :: Entity)) (gerku $x)))
         (Refer
          (λ (($reference :: (Referents Entity)))
            (∧
             (∧
              (∀ (λ (($member :: Entity)) (→ (Among $member $reference) ((λ (($x :: Entity)) (gerku $x)) $member))))
              (∀
               (λ (($subreference :: (Referents Entity)))
                 (→
                  (Among $subreference $reference)
                  (∃
                   (λ (($member :: Entity))
                     (∧
                      ((λ (($x :: Entity)) (gerku $x)) $member)
                      (∃
                       (λ (($common :: (Referents Entity)))
                         (∧ (Among $common $member) (Among $common $subreference)))))))))))
             (∀ (λ (($member :: Entity)) (→ ((λ (($x :: Entity)) (gerku $x)) $member) (Among $member $reference))))))))
        (∀
         (λ (($member :: Entity))
           (→
            (Among $member $w)
            ((λ (($x :: Entity))
               (Bind
                ($ctx3 :: (Referents Entity))
                (Context)
                (CloseClause
                 (λ (($actual_event :: (Referents Eventuality)))
                   (∧
                    ((λ (($event :: (Referents Eventuality))) (tavla $x $r $ctx3 $event)) $actual_event)
                    (fasnu $actual_event))))))
             $member)))))))))
  (case (id "635a3aa7bafa3719cc67c19e9d139aacb53252c0")
    (status available)
    (term
     (Bind
      ($r :: (Referents Entity))
      (Refer (λ (($unit :: (Referents Entity))) (mlatu $unit)))
      (Assert
       (¬
        (Bind
         ($w1 :: (Referents Entity))
         (SelectAtLeast 1 (λ (($x :: Entity)) (gerku $x)))
         ((λ (($w :: (Referents Entity)))
            (Bind
             ($ctx3 :: (Referents Entity))
             (Context)
             (CloseClause
              (λ (($actual_event :: (Referents Eventuality)))
                (∧
                 ((λ (($event :: (Referents Eventuality))) (tavla $r $w $ctx3 $event)) $actual_event)
                 (fasnu $actual_event))))))
          $w1)))))))
  (case (id "6489b84bf8e9ceae95a45d0dc9a4bed9e4eb6514")
    (status available)
    (term
     (Bind
      ($r :: (Referents Entity))
      (Refer (λ (($unit :: (Referents Entity))) (mlatu $unit)))
      (Bind
       ($nuclear_tavla_3 :: (Referents Entity))
       (Context)
       (Assert
        (=
         (Card
          (SetOf
           (λ (($global_member :: Entity))
             (∧
              ((λ (($restrictor_member :: Entity)) (gerku $restrictor_member)) $global_member)
              ((λ (($nuclear_member :: Entity))
                 (CloseClause
                  (λ (($actual_event :: (Referents Eventuality)))
                    (∧
                     ((λ (($event :: (Referents Eventuality))) (tavla $nuclear_member $r $nuclear_tavla_3 $event))
                      $actual_event)
                     (fasnu $actual_event)))))
               $global_member)))))
         3))))))
  (case (id "64c15957e568587d74aa30b873ef5aa684436258")
    (status available)
    (term
     (Bind
      ($r :: (Referents Entity))
      (Refer (λ (($unit2 :: (Referents Entity))) (prenu $unit2)))
      (Bind
       ($r1 :: (Referents Entity))
       (Refer (λ (($unit1 :: (Referents Entity))) (gerku $unit1)))
       (Bind
        ($r2 :: (Referents Entity))
        (Refer (λ (($unit :: (Referents Entity))) (mlatu $unit)))
        (Assert
         (Bind
          ($ctx4 :: (Referents Entity))
          (Context)
          ($ctx5 :: (Referents Entity))
          (Context)
          (CloseClause
           (λ (($actual_event :: (Referents Eventuality)))
             (∧
              ((λ (($event :: (Referents Eventuality))) (klama $r $r1 $r2 $ctx4 $ctx5 $event)) $actual_event)
              (fasnu $actual_event)))))))))))
  (case (id "6584fc7110a48d8b01400f0fed7714f08cf3cbac")
    (status unavailable)
    (reason
     "a0-expand-exactly: (a0-expand-exactly 0 Entity (λ (($x Entity)) (gerku $x)) (λ (($w (Referents Entity))) (Bind (($s Scale (Context))) (CloseWith (row jmaji 1 direct-event (1)) ((1 $w)))))) is not in my domain"))
  (case (id "661c26cadee3dc745ccebb82394c046d78ee79a7")
    (status available)
    (term
     (Bind
      ($r :: (Referents Entity))
      (Refer (λ (($unit1 :: (Referents Entity))) (gerku $unit1)))
      (Bind
       ($r1 :: (Referents Entity))
       (Refer (λ (($unit :: (Referents Entity))) (gerku $unit)))
       (Assert
        (Bind
         ($ctx3 :: (Referents Entity))
         (Context)
         (CloseClause
          (λ (($actual_event :: (Referents Eventuality)))
            (∧
             ((λ (($event :: (Referents Eventuality))) (tavla $r $r1 $ctx3 $event)) $actual_event)
             (fasnu $actual_event))))))))))
  (case (id "676aca15433b25852f0cb06540b381890f0b57a6")
    (status available)
    (term
     (Assert
      (CloseClause
       (λ (($actual_event :: (Referents Eventuality)))
         (∧ ((StateClause (remna (Combine Speaker Audience))) $actual_event) (fasnu $actual_event)))))))
  (case (id "68d76ee28c33ecdc9d3ddeebc06340e47b086fc9")
    (status available)
    (term
     (SetOf
      (λ (($z :: Entity))
        (¬
         (Bind
          ($w1 :: (Referents Entity))
          (SelectAtLeast 1 (λ (($x :: Entity)) (gerku $x)))
          ((λ (($w :: (Referents Entity)))
             (CloseClause
              (λ (($actual_event :: (Referents Eventuality)))
                (∧ ((λ (($event :: (Referents Eventuality))) (jmaji $w $event)) $actual_event) (fasnu $actual_event)))))
           $w1)))))))
  (case (id "6acd3321836246a9a199a76f55d4d3e00e681762")
    (status available)
    (term
     (Bind
      ($r :: (Referents Entity))
      (Refer (λ (($named :: (Referents Entity))) (Named "alis" $named)))
      (Assert
       (Bind
        ($ctx3 :: (Referents Entity))
        (Context)
        (CloseClause
         (λ (($actual_event :: (Referents Eventuality)))
           (∧
            ((λ (($event :: (Referents Eventuality))) (tavla Speaker $r $ctx3 $event)) $actual_event)
            (fasnu $actual_event)))))))))
  (case (id "6b708ddcdacf0a49ffaf55306f0cccad98046a67")
    (status available)
    (term
     (Bind
      ($purpose :: (Referents Entity))
      (Context)
      ($n :: Natural)
      (Vague (AdmissibleThreshold TooManyK (λ (($x :: Entity)) (gerku $x)) $purpose))
      (Assert
       (Bind
        ($w1 :: (Referents Entity))
        (SelectAtLeast (+ $n 1) (λ (($x :: Entity)) (gerku $x)))
        ((λ (($w :: (Referents Entity)))
           (Bind
            ($ctx3 :: (Referents Entity))
            (Context)
            (CloseClause
             (λ (($actual_event :: (Referents Eventuality)))
               (∧
                ((λ (($event :: (Referents Eventuality))) (tavla Speaker $w $ctx3 $event)) $actual_event)
                (fasnu $actual_event))))))
         $w1))))))
  (case (id "6db1d0ab2a56d4dec895dc6191ac5bc37881bc41")
    (status available)
    (term
     (Bind
      ($base :: (Referents Entity))
      (Local (Refer (λ (($x :: Entity)) (gerku $x))))
      (Bind
       ($sets :: (Referents (Set Entity)))
       (Refer
        (λ (($s :: (Set Entity)))
          (CloseClause
           (λ (($actual_event :: (Referents Eventuality)))
             (∧ ((StateClause (selcmi $s $base)) $actual_event) (fasnu $actual_event))))))
       (Mention $sets)))))
  (case (id "6dda66c58218158e235fe50e2f640eb4570dc8d9")
    (status available)
    (term
     (Bind
      ($w1 :: (Referents Entity))
      (SelectAtLeast 1 (λ (($x :: Entity)) (gerku $x)))
      ((λ (($w :: (Referents Entity)))
         (Bind
          ($ctx3 :: (Referents Entity))
          (Context)
          (CloseClause
           (λ (($actual_event :: (Referents Eventuality)))
             (∧
              ((λ (($event :: (Referents Eventuality))) (tavla $w Speaker $ctx3 $event)) $actual_event)
              (fasnu $actual_event))))))
       $w1))))
  (case (id "6e39ed994d886bf1029e9d81b13d2c4969d12f1c")
    (status available)
    (term
     (SetOf
      (λ (($z :: Entity))
        (¬
         (Bind
          ($w1 :: (Referents Entity))
          (SelectAtLeast (+ 1 1) (λ (($x :: Entity)) (gerku $x)))
          ((λ (($w :: (Referents Entity)))
             (CloseClause
              (λ (($actual_event :: (Referents Eventuality)))
                (∧ ((λ (($event :: (Referents Eventuality))) (jmaji $w $event)) $actual_event) (fasnu $actual_event)))))
           $w1)))))))
  (case (id "6e60ee9760e47fd7461b482efbc63e5c17e28444")
    (status unavailable)
    (reason
     "a0-expand-let: (a0-expand-let $a (Act Assertion) (Assert (CloseWith (row klama 5 direct-event (1 2 3 4 5)) ((1 Audience)))) (Bind (($o (ActOccurrence Assertion) (Perform Host $a))) (Do (Perform AttachedDisplay (Express (Close (Happiness Speaker $o Moderate))))))) is not in my domain"))
  (case (id "6ecb067d1e11340ae795c26b66ed1936248998a6")
    (status available)
    (term
     (Bind
      ($r :: (Referents Entity))
      (Refer (λ (($named :: (Referents Entity))) (Named "alis" $named)))
      (Assert
       (Bind
        ($w1 :: (Referents Entity))
        (SelectExactly 3 (λ (($x :: Entity)) (gerku $x)))
        ((λ (($w :: (Referents Entity)))
           (Bind
            ($ctx3 :: (Referents Entity))
            (Context)
            (CloseClause
             (λ (($actual_event :: (Referents Eventuality)))
               (∧
                ((λ (($event :: (Referents Eventuality))) (tavla $w $r $ctx3 $event)) $actual_event)
                (fasnu $actual_event))))))
         $w1))))))
  (case (id "6f6172a19fbd27927333f4dd1fa4152e9a5ae5c8")
    (status unavailable)
    (reason
     "a0-expand-let: (a0-expand-let $a1 (Act Assertion) (Assert (CloseWith (row klama 5 direct-event (1 2 3 4 5)) ((1 Speaker)))) (Bind (($o1 (ActOccurrence Assertion) (Perform Host $a1))) (Let ($a2 (Act Assertion)) (Assert (CloseWith (row stali 1 direct-event (1)) ((1 Audience)))) (Bind (($o2 (ActOccurrence Assertion) (Perform Host $a2))) (Do (Perform AttachedDisplay (Express (Close (Contrast $o2 $o1))))))))) is not in my domain"))
  (case (id "6f7179b2bc813a079360002fde1531d22f13075a")
    (status available)
    (term
     (SetOf
      (λ (($z :: Entity))
        (Bind
         ($w :: (Referents Entity))
         (Presuppose
          (∃ (λ (($x :: Entity)) (gerku $x)))
          (Refer
           (λ (($reference :: (Referents Entity)))
             (∧
              (∧
               (∀ (λ (($member :: Entity)) (→ (Among $member $reference) ((λ (($x :: Entity)) (gerku $x)) $member))))
               (∀
                (λ (($subreference :: (Referents Entity)))
                  (→
                   (Among $subreference $reference)
                   (∃
                    (λ (($member :: Entity))
                      (∧
                       ((λ (($x :: Entity)) (gerku $x)) $member)
                       (∃
                        (λ (($common :: (Referents Entity)))
                          (∧ (Among $common $member) (Among $common $subreference)))))))))))
              (∀ (λ (($member :: Entity)) (→ ((λ (($x :: Entity)) (gerku $x)) $member) (Among $member $reference))))))))
         (∀
          (λ (($member :: Entity))
            (→
             (Among $member $w)
             ((λ (($x :: Entity))
                (CloseClause
                 (λ (($actual_event :: (Referents Eventuality)))
                   (∧
                    ((λ (($event :: (Referents Eventuality))) (jmaji $x $event)) $actual_event)
                    (fasnu $actual_event)))))
              $member)))))))))
  (case (id "7093b728d78697d97257006327e2dcbdb9a365aa")
    (status available)
    (term
     (Bind
      ($restrictor_klama_2 :: (Referents Entity))
      (Context)
      ($restrictor_klama_3 :: (Referents Entity))
      (Context)
      ($restrictor_klama_4 :: (Referents Entity))
      (Context)
      ($restrictor_klama_5 :: (Referents Entity))
      (Context)
      ($nuclear_klama_2 :: (Referents Entity))
      (Context)
      ($nuclear_klama_3 :: (Referents Entity))
      (Context)
      ($nuclear_klama_4 :: (Referents Entity))
      (Context)
      ($nuclear_klama_5 :: (Referents Entity))
      (Context)
      (=
       (Card
        (SetOf
         (λ (($global_member :: Entity))
           (∧
            ((λ (($restrictor_member :: Entity))
               (CloseClause
                (λ (($actual_event :: (Referents Eventuality)))
                  (∧
                   ((λ (($event :: (Referents Eventuality)))
                      (klama
                       $restrictor_member
                       $restrictor_klama_2
                       $restrictor_klama_3
                       $restrictor_klama_4
                       $restrictor_klama_5
                       $event))
                    $actual_event)
                   (fasnu $actual_event)))))
             $global_member)
            ((λ (($nuclear_member :: Entity))
               (CloseClause
                (λ (($actual_event :: (Referents Eventuality)))
                  (∧
                   ((λ (($event :: (Referents Eventuality)))
                      (klama
                       $nuclear_member
                       $nuclear_klama_2
                       $nuclear_klama_3
                       $nuclear_klama_4
                       $nuclear_klama_5
                       $event))
                    $actual_event)
                   (fasnu $actual_event)))))
             $global_member)))))
       3))))
  (case (id "70d243e3fab7fa6f6e9075898b0883efc9ac6a64")
    (status available)
    (term
     (Bind
      ($cat :: (Referents Entity))
      (Refer (λ (($x :: (Referents Entity))) (mlatu $x)))
      (Do
       (Assert
        (CloseClause
         (λ (($actual_event :: (Referents Eventuality)))
           (∧ ((StateClause (blabi $cat)) $actual_event) (fasnu $actual_event)))))
       (Assert
        (Bind
         ($ctx2 :: (Referents Entity))
         (Context)
         ($ctx3 :: (Referents Entity))
         (Context)
         (CloseClause
          (λ (($actual_event :: (Referents Eventuality)))
            (∧
             ((λ (($event :: (Referents Eventuality))) (jbena $cat $ctx2 $ctx3 $event)) $actual_event)
             (fasnu $actual_event))))))))))
  (case (id "7318097d39a3fd427b8496b52e0a9c8c908bd088")
    (status available)
    (term
     (λ (($p :: (EFn (Entity) Content)) ($r :: (Referents Entity)))
       (∧
        (∀ (λ (($member :: Entity)) (→ (Among $member $r) ($p $member))))
        (∀
         (λ (($subreference :: (Referents Entity)))
           (→
            (Among $subreference $r)
            (∃
             (λ (($member :: Entity))
               (∧
                ($p $member)
                (∃
                 (λ (($common :: (Referents Entity)))
                   (∧ (Among $common $member) (Among $common $subreference))))))))))))))
  (case (id "7489629dc458e9a2b37b77e7009276d086528421")
    (status unavailable)
    (reason
     "b1-expand-more-than: (b1-expand-more-than 1 Entity (λ (($x Entity)) (gerku $x)) (λ (($w (Referents Entity))) (Bind (($s Scale (Context))) (CloseWith (row jmaji 1 direct-event (1)) ((1 $w)))))) is not in my domain"))
  (case (id "7668b7e50f1b89af8fbe18ec31f6edbc45b1168c")
    (status available)
    (term
     (Assert
      (Generic
       Typical
       (λ (($x :: Entity)) (mlatu $x))
       (λ (($x :: Entity))
         (Bind
          ($ctx2 :: (Referents Entity))
          (Context)
          (CloseClause
           (λ (($actual_event :: (Referents Eventuality)))
             (∧ ((StateClause (cinri $x $ctx2)) $actual_event) (fasnu $actual_event))))))))))
  (case (id "7867eb120b34ea3b161cbf57dc7c72375822f193")
    (status available)
    (term
     (Presuppose
      (∃
       (λ (($x :: Entity))
         (∧
          (prenu $x)
          (∃
           (λ (($y :: Entity))
             (∧
              (xasli $y)
              (CloseClause
               (λ (($actual_event :: (Referents Eventuality)))
                 (∧ ((StateClause (ponse $x $y)) $actual_event) (fasnu $actual_event))))))))))
      (∀
       (λ (($p :: Entity) ($d :: (Referents Entity)))
         (→
          (∧
           (prenu $p)
           (∀ (λ (($member :: Entity)) (→ (Among $member $d) ((λ (($z :: Entity)) (xasli $z)) $member))))
           (CloseClause
            (λ (($actual_event :: (Referents Eventuality)))
              (∧ ((StateClause (ponse $p $d)) $actual_event) (fasnu $actual_event)))))
          (Bind
           ($ctx3 :: (Referents Entity))
           (Context)
           (CloseClause
            (λ (($actual_event :: (Referents Eventuality)))
              (∧
               ((λ (($event :: (Referents Eventuality))) (darxi $p $d $ctx3 $event)) $actual_event)
               (fasnu $actual_event)))))))))))
  (case (id "7cccf0a9acae76bbd8db11b56c25879603ef4cff") (status available) (term (SetOf (λ (($z :: Entity)) (∧)))))
  (case (id "7d1e0a45041ecaa91bb99f88da953e476b218b8f")
    (status available)
    (term
     (λ (($bread :: (Referents Entity)) ($breadUnit :: (Fn (Entity) Content)))
       (∧
        (∧
         (∀ (λ (($member :: Entity)) (→ (Among $member $bread) ($breadUnit $member))))
         (∀
          (λ (($subreference :: (Referents Entity)))
            (→
             (Among $subreference $bread)
             (∃
              (λ (($member :: Entity))
                (∧
                 ($breadUnit $member)
                 (∃
                  (λ (($common :: (Referents Entity)))
                    (∧ (Among $common $member) (Among $common $subreference)))))))))))
        (∀
         (λ (($r :: (Referents Entity)))
           (→ (Among $r $bread) (∃ (λ (($s :: (Referents Entity))) (∧ (Among $s $r) (¬ (Among $r $s))))))))))))
  (case (id "7f097098e1315809937f245c79749a84701de106")
    (status available)
    (term
     (Generic
      Typical
      (λ (($x :: Entity)) (gerku $x))
      (λ (($x :: Entity))
        (Bind
         ($s :: Scale)
         (Context)
         (CloseClause
          (λ (($actual_event :: (Referents Eventuality)))
            (∧ ((λ (($event :: (Referents Eventuality))) (jmaji $x $event)) $actual_event) (fasnu $actual_event)))))))))
  (case (id "7f203497c357df2c9869f79e1b4eaa87c6c9de1c")
    (status available)
    (term
     (Combine
      Speaker
      (CloseClause
       (λ (($actual_event :: (Referents Eventuality)))
         (∧ ((StateClause (gerku Speaker)) $actual_event) (fasnu $actual_event)))))))
  (case (id "8061585a4f66d8b8e88b791afd3e6ad31da2df53")
    (status available)
    (term
     (Bind
      ($r :: (Referents Entity))
      (Refer (λ (($unit :: (Referents Entity))) (mlatu $unit)))
      (Assert
       (Bind
        ($w1 :: (Referents Entity))
        (SelectExactly 3 (λ (($x :: Entity)) (gerku $x)))
        ((λ (($w :: (Referents Entity)))
           (Bind
            ($ctx3 :: (Referents Entity))
            (Context)
            (CloseClause
             (λ (($actual_event :: (Referents Eventuality)))
               (∧
                ((λ (($event :: (Referents Eventuality))) (tavla $r $w $ctx3 $event)) $actual_event)
                (fasnu $actual_event))))))
         $w1))))))
  (case (id "808a6f9bdbbb1073dda1dc3a393dee0026919d4f")
    (status available)
    (term
     (Bind
      ($restrictor_klama_2 :: (Referents Entity))
      (Context)
      ($restrictor_klama_3 :: (Referents Entity))
      (Context)
      ($restrictor_klama_4 :: (Referents Entity))
      (Context)
      ($restrictor_klama_5 :: (Referents Entity))
      (Context)
      ($nuclear_bajra_2 :: (Referents Entity))
      (Context)
      ($nuclear_bajra_3 :: (Referents Entity))
      (Context)
      ($nuclear_bajra_4 :: (Referents Entity))
      (Context)
      (=
       (Card
        (SetOf
         (λ (($global_member :: Entity))
           (∧
            ((λ (($restrictor_member :: Entity))
               (CloseClause
                (λ (($actual_event :: (Referents Eventuality)))
                  (∧
                   ((λ (($event :: (Referents Eventuality)))
                      (klama
                       $restrictor_member
                       $restrictor_klama_2
                       $restrictor_klama_3
                       $restrictor_klama_4
                       $restrictor_klama_5
                       $event))
                    $actual_event)
                   (fasnu $actual_event)))))
             $global_member)
            ((λ (($nuclear_member :: Entity))
               (CloseClause
                (λ (($actual_event :: (Referents Eventuality)))
                  (∧
                   ((λ (($event :: (Referents Eventuality)))
                      (bajra $nuclear_member $nuclear_bajra_2 $nuclear_bajra_3 $nuclear_bajra_4 $event))
                    $actual_event)
                   (fasnu $actual_event)))))
             $global_member)))))
       3))))
  (case (id "80b377eeaeeff358d3b8c1f73fd2749ffb17cb57")
    (status unavailable)
    (reason
     "a0-expand-exactly: (a0-expand-exactly 1 Entity (λ (($x Entity)) (gerku $x)) (λ (($w (Referents Entity))) (Bind (($s Scale (Context))) (CloseWith (row jmaji 1 direct-event (1)) ((1 $w)))))) is not in my domain"))
  (case (id "81d3fa49e84bfcf00813d35fad8d70b23b8d3935")
    (status available)
    (term
     (=
      (Card
       (SetOf
        (λ (($global_member :: Entity))
          (∧
           ((λ (($x :: Entity)) (gerku $x)) $global_member)
           ((λ (($x :: Entity))
              (CloseClause
               (λ (($actual_event :: (Referents Eventuality)))
                 (∧
                  ((λ (($event :: (Referents Eventuality))) (jmaji $x $event)) $actual_event)
                  (fasnu $actual_event)))))
            $global_member)))))
      1)))
  (case (id "8360021fa7e50952cd0f155fbb5c8ea9a845b60f")
    (status available)
    (term
     (SentenceSign
      (CloseClause
       (λ (($actual_event :: (Referents Eventuality)))
         (∧ ((StateClause (gerku Speaker)) $actual_event) (fasnu $actual_event)))))))
  (case (id "8447f6258b31394149ce313493c037835dfbdc08")
    (status available)
    (term
     (=
      (Card
       (SetOf
        (λ (($global_member :: Entity))
          (∧ ((λ (($p :: Entity)) (prenu $p)) $global_member) ((λ (($q :: Entity)) (blabi $q)) $global_member)))))
      2)))
  (case (id "84d3f3f5db6d9bb097e9df301673052e73e0649a")
    (status available)
    (term
     (SetOf
      (λ (($x :: Entity))
        (Bind ($r :: (Referents Entity)) (SelectAtLeast 1 (λ (($y :: Entity)) (gerku $y))) (gerku $x))))))
  (case (id "8ccd154413e727b9b34e8a038b034866944e530b")
    (status unavailable)
    (reason
     "b1-expand-at-least: no clauses matched for (b1-expand-at-least $n Entity (λ (($x Entity)) (gerku $x)) (λ (($w (Referents Entity))) (CloseWith (row tavla 3 direct-event (1 2 3)) ((1 $w) (2 $r)))))"))
  (case (id "8e1fab41bbb56ee118edf789bec2b290dedfaa2e")
    (status unavailable)
    (reason
     "b1-expand-more-than: (b1-expand-more-than 1 Entity (λ (($x Entity)) (Bind (($s Scale (Context))) (gerku $x))) (λ (($w (Referents Entity))) (CloseWith (row jmaji 1 direct-event (1)) ((1 $w))))) is not in my domain"))
  (case (id "90ea9f4b3bd16e1989e5d78f7db1bfc8698c46bd")
    (status available)
    (term
     (Bind
      ($nuclear_bajra_2 :: (Referents Entity))
      (Context)
      ($nuclear_bajra_3 :: (Referents Entity))
      (Context)
      ($nuclear_bajra_4 :: (Referents Entity))
      (Context)
      (Assert
       (=
        (Card
         (SetOf
          (λ (($global_member :: Entity))
            (∧
             ((λ (($restrictor_member :: Entity)) (gerku $restrictor_member)) $global_member)
             ((λ (($nuclear_member :: Entity))
                (CloseClause
                 (λ (($actual_event :: (Referents Eventuality)))
                   (∧
                    ((λ (($event :: (Referents Eventuality)))
                       (bajra $nuclear_member $nuclear_bajra_2 $nuclear_bajra_3 $nuclear_bajra_4 $event))
                     $actual_event)
                    (fasnu $actual_event)))))
              $global_member)))))
        3)))))
  (case (id "94cf88a0926fcd3b3ed426e8325e749edea9ed95")
    (status unavailable)
    (reason
     "b1-expand-at-least: (b1-expand-at-least 1 Entity (λ (($x Entity)) (Bind (($s Scale (Context))) (gerku $x))) (λ (($w (Referents Entity))) (CloseWith (row jmaji 1 direct-event (1)) ((1 $w))))) is not in my domain"))
  (case (id "9950bcb96b07982d231b52cb8af364c40cb79561")
    (status available)
    (term
     (Bind
      ($w1 :: (Referents Entity))
      (Presuppose
       (∃ (λ (($x :: Entity)) (gerku $x)))
       (Refer
        (λ (($reference :: (Referents Entity)))
          (∧
           (∧
            (∀ (λ (($member :: Entity)) (→ (Among $member $reference) ((λ (($x :: Entity)) (gerku $x)) $member))))
            (∀
             (λ (($subreference :: (Referents Entity)))
               (→
                (Among $subreference $reference)
                (∃
                 (λ (($member :: Entity))
                   (∧
                    ((λ (($x :: Entity)) (gerku $x)) $member)
                    (∃
                     (λ (($common :: (Referents Entity)))
                       (∧ (Among $common $member) (Among $common $subreference)))))))))))
           (∀ (λ (($member :: Entity)) (→ ((λ (($x :: Entity)) (gerku $x)) $member) (Among $member $reference))))))))
      (∀
       (λ (($member :: Entity))
         (→
          (Among $member $w1)
          ((λ (($w :: (Referents Entity)))
             (CloseClause
              (λ (($actual_event :: (Referents Eventuality)))
                (∧ ((λ (($event :: (Referents Eventuality))) (jmaji $w $event)) $actual_event) (fasnu $actual_event)))))
           $member)))))))
  (case (id "997aadf61f2b9a8b77acdb90390719fef358c2b5")
    (status available)
    (term
     (Bind
      ($r :: (Referents Entity))
      (Refer (λ (($unit :: (Referents Entity))) (mlatu $unit)))
      (Assert
       (Bind
        ($w1 :: (Referents Entity))
        (SelectExactly 3 (λ (($x :: Entity)) (gerku $x)))
        ((λ (($w :: (Referents Entity)))
           (Bind
            ($ctx3 :: (Referents Entity))
            (Context)
            (CloseClause
             (λ (($actual_event :: (Referents Eventuality)))
               (∧
                ((λ (($event :: (Referents Eventuality))) (tavla $w $r $ctx3 $event)) $actual_event)
                (fasnu $actual_event))))))
         $w1))))))
  (case (id "9a6d68b66792504622ef5443bf9cdab8db165f01")
    (status available)
    (term
     (λ (($x :: (Referents Entity)))
       (Bind
        ($ctx1 :: (Referents Entity))
        (Context)
        ($ctx3 :: (Referents Entity))
        (Context)
        ($ctx4 :: (Referents Entity))
        (Context)
        ($ctx5 :: (Referents Entity))
        (Context)
        (CloseClause
         (λ (($actual_event :: (Referents Eventuality)))
           (∧
            ((λ (($event :: (Referents Eventuality))) (klama $ctx1 $x $ctx3 $ctx4 $ctx5 $event)) $actual_event)
            (fasnu $actual_event))))))))
  (case (id "9c1407e2953b9b8ea62d6c2623bf886058927595")
    (status available)
    (term
     (Bind
      ($r :: (Referents Entity))
      (Refer (λ (($unit :: (Referents Entity))) (gerku $unit)))
      (Assert
       (CloseClause
        (λ (($actual_event :: (Referents Eventuality)))
          (∧ ((StateClause (blabi $r)) $actual_event) (fasnu $actual_event))))))))
  (case (id "9d479ff45f970013a08eaf988ae266bddb2e6820")
    (status available)
    (term
     (Bind
      ($r :: (Referents Entity))
      (Refer (λ (($named :: (Referents Entity))) (Named "alis" $named)))
      (Assert
       (Bind
        ($w1 :: (Referents Entity))
        (SelectExactly 3 (λ (($x :: Entity)) (gerku $x)))
        ((λ (($w :: (Referents Entity)))
           (Bind
            ($ctx3 :: (Referents Entity))
            (Context)
            (CloseClause
             (λ (($actual_event :: (Referents Eventuality)))
               (∧
                ((λ (($event :: (Referents Eventuality))) (tavla $r $w $ctx3 $event)) $actual_event)
                (fasnu $actual_event))))))
         $w1))))))
  (case (id "9e06566d9890b2c704417adef0a5b50d9cdcd8e4")
    (status available)
    (term
     (Bind
      ($nuclear_bajra_2 :: (Referents Entity))
      (Context)
      ($nuclear_bajra_3 :: (Referents Entity))
      (Context)
      ($nuclear_bajra_4 :: (Referents Entity))
      (Context)
      (=
       (Card
        (SetOf
         (λ (($global_member :: Entity))
           (∧
            ((λ (($restrictor_member :: Entity)) (gerku $restrictor_member)) $global_member)
            ((λ (($nuclear_member :: Entity))
               (CloseClause
                (λ (($actual_event :: (Referents Eventuality)))
                  (∧
                   ((λ (($event :: (Referents Eventuality)))
                      (bajra $nuclear_member $nuclear_bajra_2 $nuclear_bajra_3 $nuclear_bajra_4 $event))
                    $actual_event)
                   (fasnu $actual_event)))))
             $global_member)))))
       3))))
  (case (id "9e1244208e96d43b67c311bf34bbe418b2a02514")
    (status available)
    (term
     (Bind
      ($cat :: (Referents Entity))
      (Refer (λ (($x :: (Referents Entity))) (∧ (mlatu $x) (blabi $x))))
      (Assert
       (Bind
        ($ctx2 :: (Referents Entity))
        (Context)
        ($ctx3 :: (Referents Entity))
        (Context)
        (CloseClause
         (λ (($actual_event :: (Referents Eventuality)))
           (∧
            ((λ (($event :: (Referents Eventuality))) (jbena $cat $ctx2 $ctx3 $event)) $actual_event)
            (fasnu $actual_event)))))))))
  (case (id "9eb692db840e8b2093a85c697191a3a561335644")
    (status available)
    (term
     (Bind
      ($nuclear_tavla_3 :: (Referents Entity))
      (Context)
      (Assert
       (=
        (Card
         (SetOf
          (λ (($global_member :: Entity))
            (∧
             ((λ (($restrictor_member :: Entity)) (gerku $restrictor_member)) $global_member)
             ((λ (($nuclear_member :: Entity))
                (CloseClause
                 (λ (($actual_event :: (Referents Eventuality)))
                   (∧
                    ((λ (($event :: (Referents Eventuality))) (tavla Speaker $nuclear_member $nuclear_tavla_3 $event))
                     $actual_event)
                    (fasnu $actual_event)))))
              $global_member)))))
        3)))))
  (case (id "a13da18fac2b9d1a13e06cf1ecc0c540d5adf01e")
    (status unavailable)
    (reason
     "b1-expand-fewer-than: (b1-expand-fewer-than 1 Entity (λ (($x Entity)) (gerku $x)) (λ (($w (Referents Entity))) (Bind (($s Scale (Context))) (CloseWith (row jmaji 1 direct-event (1)) ((1 $w)))))) is not in my domain"))
  (case (id "a276ef47aa851126f08e68dcf950821a4344f119")
    (status unavailable)
    (reason
     "b1-expand-fewer-than: (b1-expand-fewer-than 1 Entity (λ (($x Entity)) (Bind (($s Scale (Context))) (gerku $x))) (λ (($w (Referents Entity))) (CloseWith (row jmaji 1 direct-event (1)) ((1 $w))))) is not in my domain"))
  (case (id "a52f77e5f64ace85eb112472d016486a31befafa")
    (status available)
    (term
     (Bind
      ($left :: (Referents Entity))
      (SelectExactly 3 (λ (($x :: Entity)) (gerku $x)))
      ($right :: (Referents Entity))
      (SelectExactly 2 (λ (($x1 :: Entity)) (prenu $x1)))
      (Mention
       (∀
        (λ (($member :: Entity))
          (→
           (Among $member $left)
           ((λ (($l :: Entity))
              (∀
               (λ (($member :: Entity))
                 (→
                  (Among $member $right)
                  ((λ (($r :: Entity))
                     (CloseClause
                      (λ (($actual_event :: (Referents Eventuality)))
                        (∧ ((StateClause (nelci $l $r)) $actual_event) (fasnu $actual_event)))))
                   $member)))))
            $member))))))))
  (case (id "a6c8d36f67dc1c2896c84ec3fa881889f761b7d4")
    (status available)
    (term
     (Assert
      (¬
       (Bind
        ($w1 :: (Referents Entity))
        (SelectAtLeast 1 (λ (($x :: Entity)) (gerku $x)))
        ((λ (($w :: (Referents Entity)))
           (Bind
            ($ctx3 :: (Referents Entity))
            (Context)
            (CloseClause
             (λ (($actual_event :: (Referents Eventuality)))
               (∧
                ((λ (($event :: (Referents Eventuality))) (tavla Speaker $w $ctx3 $event)) $actual_event)
                (fasnu $actual_event))))))
         $w1))))))
  (case (id "a80380a1b22f80fe8a622376789319b054091307")
    (status available)
    (term
     (Mention
      (Bind
       ($w1 :: (Referents Entity))
       (SelectAtLeast 1 (λ (($x :: Entity)) (gerku $x)))
       ((λ (($w :: (Referents Entity)))
          (Bind
           ($ctx3 :: (Referents Entity))
           (Context)
           (CloseClause
            (λ (($actual_event :: (Referents Eventuality)))
              (∧
               ((λ (($event :: (Referents Eventuality))) (tavla $w Speaker $ctx3 $event)) $actual_event)
               (fasnu $actual_event))))))
        $w1)))))
  (case (id "adaf5b13f560e52ca23d027a2d22093fa35294bb")
    (status unavailable)
    (reason
     "b1-expand-at-least: no clauses matched for (b1-expand-at-least $n Entity (λ (($x Entity)) (mlatu $x)) (λ (($w (Referents Entity))) (CloseWith (row tavla 3 direct-event (1 2 3)) ((1 $r) (2 $w)))))"))
  (case (id "ae0905b127f17eec2dd17799de3b6e64a28f0423")
    (status available)
    (term
     (Bind
      ($purpose :: (Referents Entity))
      (Context)
      ($n :: Natural)
      (Vague (AdmissibleThreshold TooManyK (λ (($x :: Entity)) (gerku $x)) $purpose))
      (Assert
       (Bind
        ($w1 :: (Referents Entity))
        (SelectAtLeast (+ $n 1) (λ (($x :: Entity)) (gerku $x)))
        ((λ (($w :: (Referents Entity)))
           (Bind
            ($ctx2 :: (Referents Entity))
            (Context)
            ($ctx3 :: (Referents Entity))
            (Context)
            ($ctx4 :: (Referents Entity))
            (Context)
            ($ctx5 :: (Referents Entity))
            (Context)
            (CloseClause
             (λ (($actual_event :: (Referents Eventuality)))
               (∧
                ((λ (($event :: (Referents Eventuality))) (klama $w $ctx2 $ctx3 $ctx4 $ctx5 $event)) $actual_event)
                (fasnu $actual_event))))))
         $w1))))))
  (case (id "afdc655e5d92abe64d7f60264ba07d4e6d7aac18")
    (status available)
    (term
     (Bind
      ($nuclear_bajra_2 :: (Referents Entity))
      (Context)
      ($nuclear_bajra_3 :: (Referents Entity))
      (Context)
      ($nuclear_bajra_4 :: (Referents Entity))
      (Context)
      (Mention
       (=
        (Card
         (SetOf
          (λ (($global_member :: Entity))
            (∧
             ((λ (($restrictor_member :: Entity)) (gerku $restrictor_member)) $global_member)
             ((λ (($nuclear_member :: Entity))
                (CloseClause
                 (λ (($actual_event :: (Referents Eventuality)))
                   (∧
                    ((λ (($event :: (Referents Eventuality)))
                       (bajra $nuclear_member $nuclear_bajra_2 $nuclear_bajra_3 $nuclear_bajra_4 $event))
                     $actual_event)
                    (fasnu $actual_event)))))
              $global_member)))))
        3)))))
  (case (id "b03bdb8567704858bc0414f946cd16154278b6ca")
    (status available)
    (term
     (Mention
      (λ (($x :: (Referents Entity)))
        (Bind
         ($ctx1 :: (Referents Entity))
         (Context)
         ($ctx3 :: (Referents Entity))
         (Context)
         ($ctx4 :: (Referents Entity))
         (Context)
         ($ctx5 :: (Referents Entity))
         (Context)
         (CloseClause
          (λ (($actual_event :: (Referents Eventuality)))
            (∧
             ((λ (($event :: (Referents Eventuality))) (klama $ctx1 $x $ctx3 $ctx4 $ctx5 $event)) $actual_event)
             (fasnu $actual_event)))))))))
  (case (id "b4f5a39f1b309245b2d50930cb69faed4a7b4716")
    (status unavailable)
    (reason "m2-oracle: Close has no adapter-supplied lexical row declaration"))
  (case (id "b92059ed2600b14c09f0cbb9515567e36d32a11b")
    (status available)
    (term
     (Assert
      (¬
       (Bind
        ($w1 :: (Referents Entity))
        (SelectAtLeast 1 (λ (($x :: Entity)) (gerku $x)))
        ((λ (($w :: (Referents Entity)))
           (Bind
            ($ctx3 :: (Referents Entity))
            (Context)
            (CloseClause
             (λ (($actual_event :: (Referents Eventuality)))
               (∧
                ((λ (($event :: (Referents Eventuality))) (tavla $w Speaker $ctx3 $event)) $actual_event)
                (fasnu $actual_event))))))
         $w1))))))
  (case (id "b96bfb9de1d104d2377dbf04658ed8c492dcde96")
    (status available)
    (term
     (Bind
      ($r :: (Referents Entity))
      (Refer (λ (($unit1 :: (Referents Entity))) (gerku $unit1)))
      (Bind
       ($r1 :: (Referents Entity))
       (Refer (λ (($unit :: (Referents Entity))) (mlatu $unit)))
       (Assert
        (Bind
         ($ctx3 :: (Referents Entity))
         (Context)
         (CloseClause
          (λ (($actual_event :: (Referents Eventuality)))
            (∧
             ((λ (($event :: (Referents Eventuality))) (tavla $r $r1 $ctx3 $event)) $actual_event)
             (fasnu $actual_event))))))))))
  (case (id "bb1ea3fc5780f5d106de8232523d33221406da46")
    (status available)
    (term
     (Bind
      ($r :: (Referents Entity))
      (Refer (λ (($unit :: (Referents Entity))) (mlatu $unit)))
      (Assert
       (Bind
        ($w1 :: (Referents Entity))
        (SelectAtLeast 1 (λ (($x :: Entity)) (gerku $x)))
        ((λ (($w :: (Referents Entity)))
           (Bind
            ($ctx3 :: (Referents Entity))
            (Context)
            (CloseClause
             (λ (($actual_event :: (Referents Eventuality)))
               (∧
                ((λ (($event :: (Referents Eventuality))) (tavla $w $r $ctx3 $event)) $actual_event)
                (fasnu $actual_event))))))
         $w1))))))
  (case (id "bd272fdf0064b6f7f1a30d72aaa6909228be68f7")
    (status available)
    (term
     (Bind
      ($bob :: (Referents Entity))
      (Refer (λ (($x :: (Referents Entity))) (Named "bab" $x)))
      (Do
       (Assert
        (Bind
         ($ctx2 :: (Referents Entity))
         (Context)
         ($ctx3 :: (Referents Entity))
         (Context)
         ($ctx4 :: (Referents Entity))
         (Context)
         ($ctx5 :: (Referents Entity))
         (Context)
         (CloseClause
          (λ (($actual_event :: (Referents Eventuality)))
            (∧
             ((λ (($event :: (Referents Eventuality))) (klama $bob $ctx2 $ctx3 $ctx4 $ctx5 $event)) $actual_event)
             (fasnu $actual_event))))))
       (Assert
        (Bind
         ($ctx2 :: (Referents Entity))
         (Context)
         (CloseClause
          (λ (($actual_event :: (Referents Eventuality)))
            (∧ ((StateClause (prami $bob $ctx2)) $actual_event) (fasnu $actual_event))))))))))
  (case (id "c09304c3c5c8c1202284e2acc37d191b7a50bb11")
    (status available)
    (term
     (Bind
      ($r :: (Referents Entity))
      (Refer (λ (($unit :: (Referents Entity))) (mlatu $unit)))
      (Bind
       ($nuclear_tavla_3 :: (Referents Entity))
       (Context)
       (Assert
        (=
         (Card
          (SetOf
           (λ (($global_member :: Entity))
             (∧
              ((λ (($restrictor_member :: Entity)) (gerku $restrictor_member)) $global_member)
              ((λ (($nuclear_member :: Entity))
                 (CloseClause
                  (λ (($actual_event :: (Referents Eventuality)))
                    (∧
                     ((λ (($event :: (Referents Eventuality))) (tavla $r $nuclear_member $nuclear_tavla_3 $event))
                      $actual_event)
                     (fasnu $actual_event)))))
               $global_member)))))
         3))))))
  (case (id "c27acb49649a24ec94cecaf88567f2d8e9165026")
    (status available)
    (term
     (Bind
      ($w :: (Referents Entity))
      (SelectExactly 3 (λ (($x :: Entity)) (gerku $x)))
      (Bind
       ($ctx2 :: (Referents Entity))
       (Context)
       ($ctx3 :: (Referents Entity))
       (Context)
       ($ctx4 :: (Referents Entity))
       (Context)
       (CloseClause
        (λ (($actual_event :: (Referents Eventuality)))
          (∧
           ((λ (($event :: (Referents Eventuality))) (bajra $w $ctx2 $ctx3 $ctx4 $event)) $actual_event)
           (fasnu $actual_event))))))))
  (case (id "c2893c48f65e9358154c3c71c07d9f10e125e8b4")
    (status available)
    (term
     (Assert
      (Bind
       ($w2 :: (Referents Entity))
       (SelectExactly 3 (λ (($x :: Entity)) (gerku $x)))
       ((λ (($w :: (Referents Entity)))
          (Bind
           ($w2 :: (Referents Entity))
           (SelectExactly 2 (λ (($x :: Entity)) (mlatu $x)))
           ((λ (($w1 :: (Referents Entity)))
              (Bind
               ($ctx3 :: (Referents Entity))
               (Context)
               (CloseClause
                (λ (($actual_event :: (Referents Eventuality)))
                  (∧
                   ((λ (($event :: (Referents Eventuality))) (tavla $w $w1 $ctx3 $event)) $actual_event)
                   (fasnu $actual_event))))))
            $w2)))
        $w2)))))
  (case (id "c3ef43fc929c9a2356838ee5d5de4bea0a7d5b0d")
    (status unavailable)
    (reason "m2-oracle: Close has no adapter-supplied lexical row declaration"))
  (case (id "c3f807759c2a4b21cc592b0ff7b4858dbd44f1a8")
    (status unavailable)
    (reason
     "a0-expand-let: (a0-expand-let $prior (Act Assertion) (Assert (CloseWith (row klama 5 direct-event (1 2 3 4 5)) ((1 Audience)))) (Bind (($prioro (ActOccurrence Assertion) (Perform Host $prior))) (Bind (($defect DefectKind (Context))) (Express (Close (MetalinguisticallyDefective $prioro $defect)))))) is not in my domain"))
  (case (id "c5058c35cd20c0e848804a9b2e0fa31c745e3885")
    (status available)
    (term
     (λ (($p :: (Fn (Entity) Content)) ($r :: (Referents Entity)))
       (∧
        (∀ (λ (($member :: Entity)) (→ (Among $member $r) ($p $member))))
        (∀
         (λ (($subreference :: (Referents Entity)))
           (→
            (Among $subreference $r)
            (∃
             (λ (($member :: Entity))
               (∧
                ($p $member)
                (∃
                 (λ (($common :: (Referents Entity)))
                   (∧ (Among $common $member) (Among $common $subreference))))))))))))))
  (case (id "c514182c124a29774fb65f68a9f1b73a31b5130b")
    (status available)
    (term
     (λ (($k :: (DecompositionBasis (Group Entity) Entity)))
       (Bind
        ($g :: (Referents (Group Entity)))
        (SelectExactly
         1
         (λ (($group :: (Group Entity)))
           (∧
            (Aggregate $k $group)
            (∧
             (∀
              (λ (($basis_unit :: (Referents Entity)))
                (→
                 (BasisUnitAt $k $basis_unit Speaker)
                 (∃
                  (λ (($peer_unit :: (Referents Entity)))
                    (∧
                     (PeerUnitAt $k $peer_unit $group)
                     (∧ (Among $basis_unit $peer_unit) (Among $peer_unit $basis_unit))))))))
             (∀
              (λ (($complete_peer :: (Referents Entity)))
                (→
                 (PeerUnitAt $k $complete_peer $group)
                 (∃
                  (λ (($complete_unit :: (Referents Entity)))
                    (∧
                     (BasisUnitAt $k $complete_unit Speaker)
                     (∧ (Among $complete_unit $complete_peer) (Among $complete_peer $complete_unit))))))))))))
        (Mention $g)))))
  (case (id "cb0c2d14a541bd5721c594d8492a196ae21fc449")
    (status available)
    (term
     ((λ (($a :: (Act Assertion))) (Do (Perform $a) (Perform $a)))
      (Assert
       (Bind
        ($ctx2 :: (Referents Entity))
        (Context)
        ($ctx3 :: (Referents Entity))
        (Context)
        ($ctx4 :: (Referents Entity))
        (Context)
        ($ctx5 :: (Referents Entity))
        (Context)
        (CloseClause
         (λ (($actual_event :: (Referents Eventuality)))
           (∧
            ((λ (($event :: (Referents Eventuality))) (klama Speaker $ctx2 $ctx3 $ctx4 $ctx5 $event)) $actual_event)
            (fasnu $actual_event)))))))))
  (case (id "cb238239f922d167cfddd4bbb3dfeaea323ce103")
    (status unavailable)
    (reason "m2-oracle: Massify basis type unavailable"))
  (case (id "cb8093665b4b7ed893a755ddf7595d703673c951")
    (status available)
    (term
     (SetOf
      (λ (($z :: Entity))
        (Bind
         ($w1 :: (Referents Entity))
         (SelectAtLeast 1 (λ (($x :: Entity)) (gerku $x)))
         ((λ (($w :: (Referents Entity)))
            (CloseClause
             (λ (($actual_event :: (Referents Eventuality)))
               (∧ ((λ (($event :: (Referents Eventuality))) (jmaji $w $event)) $actual_event) (fasnu $actual_event)))))
          $w1))))))
  (case (id "cf2374e6e207721068753ffa99278a37b7d56886")
    (status available)
    (term
     (Assert
      (Bind
       ($w :: (Referents Entity))
       (Presuppose
        (∃ (λ (($x :: Entity)) (gerku $x)))
        (Refer
         (λ (($reference :: (Referents Entity)))
           (∧
            (∧
             (∀ (λ (($member :: Entity)) (→ (Among $member $reference) ((λ (($x :: Entity)) (gerku $x)) $member))))
             (∀
              (λ (($subreference :: (Referents Entity)))
                (→
                 (Among $subreference $reference)
                 (∃
                  (λ (($member :: Entity))
                    (∧
                     ((λ (($x :: Entity)) (gerku $x)) $member)
                     (∃
                      (λ (($common :: (Referents Entity)))
                        (∧ (Among $common $member) (Among $common $subreference)))))))))))
            (∀ (λ (($member :: Entity)) (→ ((λ (($x :: Entity)) (gerku $x)) $member) (Among $member $reference))))))))
       (∀
        (λ (($member :: Entity))
          (→
           (Among $member $w)
           ((λ (($x :: Entity))
              (Bind
               ($ctx3 :: (Referents Entity))
               (Context)
               (CloseClause
                (λ (($actual_event :: (Referents Eventuality)))
                  (∧
                   ((λ (($event :: (Referents Eventuality))) (tavla Speaker $x $ctx3 $event)) $actual_event)
                   (fasnu $actual_event))))))
            $member))))))))
  (case (id "d12cc9e49c7b44ac7c5244121e90ff57baa5d4a7")
    (status unavailable)
    (reason
     "b1-expand-at-most: (b1-expand-at-most 1 Entity (λ (($x Entity)) (Bind (($s Scale (Context))) (gerku $x))) (λ (($w (Referents Entity))) (CloseWith (row jmaji 1 direct-event (1)) ((1 $w))))) is not in my domain"))
  (case (id "d6acabd21a4c2aef89fc166afdabe8cb838beaa1")
    (status available)
    (term
     (Bind
      ($r :: (Referents Entity))
      (Refer (λ (($unit :: (Referents Entity))) (mlatu $unit)))
      (Assert
       (¬
        (Bind
         ($w1 :: (Referents Entity))
         (SelectAtLeast 1 (λ (($x :: Entity)) (gerku $x)))
         ((λ (($w :: (Referents Entity)))
            (Bind
             ($ctx3 :: (Referents Entity))
             (Context)
             (CloseClause
              (λ (($actual_event :: (Referents Eventuality)))
                (∧
                 ((λ (($event :: (Referents Eventuality))) (tavla $w $r $ctx3 $event)) $actual_event)
                 (fasnu $actual_event))))))
          $w1)))))))
  (case (id "d7c04355b8abb979b3e68ab4cb224f4617b83534")
    (status available)
    (term
     (Bind
      ($r :: (Referents Entity))
      (Refer (λ (($unit :: (Referents Entity))) (mlatu $unit)))
      (Assert
       (Bind
        ($w1 :: (Referents Entity))
        (SelectAtLeast 1 (λ (($x :: Entity)) (gerku $x)))
        ((λ (($w :: (Referents Entity)))
           (Bind
            ($ctx3 :: (Referents Entity))
            (Context)
            (CloseClause
             (λ (($actual_event :: (Referents Eventuality)))
               (∧
                ((λ (($event :: (Referents Eventuality))) (tavla $r $w $ctx3 $event)) $actual_event)
                (fasnu $actual_event))))))
         $w1))))))
  (case (id "d8e9f58244e983851351b588de235d4375f926f0")
    (status available)
    (term
     (λ (($p :: (Fn (Eventuality) Content)) ($r :: (Referents Entity)))
       (∧
        (∀ (λ (($member :: Eventuality)) (→ (Among $member $r) ($p $member))))
        (∀
         (λ (($subreference :: (Referents Eventuality)))
           (→
            (Among $subreference $r)
            (∃
             (λ (($member :: Eventuality))
               (∧
                ($p $member)
                (∃
                 (λ (($common :: (Referents Eventuality)))
                   (∧ (Among $common $member) (Among $common $subreference))))))))))))))
  (case (id "d9e452a092108b6bfaec9670967ce2aa285e61d4")
    (status available)
    (term
     (Ask
      (OpenQ
       (λ (($x :: (Referents Entity)))
         (Bind
          ($ctx2 :: (Referents Entity))
          (Context)
          ($ctx3 :: (Referents Entity))
          (Context)
          ($ctx4 :: (Referents Entity))
          (Context)
          ($ctx5 :: (Referents Entity))
          (Context)
          (CloseClause
           (λ (($actual_event :: (Referents Eventuality)))
             (∧
              ((λ (($event :: (Referents Eventuality))) (klama $x $ctx2 $ctx3 $ctx4 $ctx5 $event)) $actual_event)
              (fasnu $actual_event))))))))))
  (case (id "da97e598f0594e6ba811953858f978a3c3a9528f")
    (status available)
    (term
     (Assert
      (¬
       (Bind
        ($w1 :: (Referents Entity))
        (SelectAtLeast 1 (λ (($x :: Entity)) (prenu $x)))
        ((λ (($w :: (Referents Entity)))
           (CloseClause
            (λ (($actual_event :: (Referents Eventuality)))
              (∧ ((λ (($event :: (Referents Eventuality))) (jmaji $w $event)) $actual_event) (fasnu $actual_event)))))
         $w1))))))
  (case (id "db9e84ebb83dc304f85923c2946dc35e1a13993e")
    (status available)
    (term
     (Bind
      ($nuclear_bajra_2 :: (Referents Entity))
      (Context)
      ($nuclear_bajra_3 :: (Referents Entity))
      (Context $nuclear_bajra_2)
      ($nuclear_bajra_4 :: (Referents Entity))
      (Context)
      (=
       (Card
        (SetOf
         (λ (($global_member :: Entity))
           (∧
            ((λ (($restrictor_member :: Entity)) (gerku $restrictor_member)) $global_member)
            ((λ (($nuclear_member :: Entity))
               (CloseClause
                (λ (($actual_event :: (Referents Eventuality)))
                  (∧
                   ((λ (($event :: (Referents Eventuality)))
                      (bajra $nuclear_member $nuclear_bajra_2 $nuclear_bajra_3 $nuclear_bajra_4 $event))
                    $actual_event)
                   (fasnu $actual_event)))))
             $global_member)))))
       3))))
  (case (id "dd044fa4f64eeccef4d68d8a20fccc9210219397")
    (status available)
    (term
     (Bind
      ($cat :: (Referents Entity))
      (Refer (λ (($x :: (Referents Entity))) (mlatu $x)))
      (Assert
       (CloseClause
        (λ (($actual_event :: (Referents Eventuality)))
          (∧ ((StateClause (blabi $cat)) $actual_event) (fasnu $actual_event))))))))
  (case (id "e23de12dfd8d47e7979803ed3f6c7f0f7b6517fa")
    (status available)
    (term
     (Generic
      Typical
      (λ (($x :: Entity)) (Bind ($s :: Scale) (Context) (gerku $x)))
      (λ (($x :: Entity))
        (CloseClause
         (λ (($actual_event :: (Referents Eventuality)))
           (∧ ((λ (($event :: (Referents Eventuality))) (jmaji $x $event)) $actual_event) (fasnu $actual_event))))))))
  (case (id "e265f654d73091e8db042b5820cba0df47e812be")
    (status unavailable)
    (reason
     "a0-expand-let: (a0-expand-let $a (Act Assertion) (Assert (CloseWith (row cadzu 4 direct-event (1 2 3 4)) ((1 Audience)))) (Bind (($o (ActOccurrence Assertion) (Perform Host $a))) (Do (Perform AttachedDisplay (Express (Close (EvidentialBasis Speaker $o Observation))))))) is not in my domain"))
  (case (id "e4a28c0b1783335f69507f29ca64cc782b80c7be")
    (status available)
    (term
     (Bind
      ($dogs :: (Referents Entity))
      (SelectExactly 3 (λ (($x :: Entity)) (gerku $x)))
      (Do
       (Assert
        (Bind
         ($ctx2 :: (Referents Entity))
         (Context)
         ($ctx3 :: (Referents Entity))
         (Context)
         ($ctx4 :: (Referents Entity))
         (Context)
         (CloseClause
          (λ (($actual_event :: (Referents Eventuality)))
            (∧
             ((λ (($event :: (Referents Eventuality))) (bajra $dogs $ctx2 $ctx3 $ctx4 $event)) $actual_event)
             (fasnu $actual_event))))))
       (Assert
        (CloseClause
         (λ (($actual_event :: (Referents Eventuality)))
           (∧ ((StateClause (tatpi $dogs)) $actual_event) (fasnu $actual_event)))))))))
  (case (id "e666727fbb4c77fa54491719b49600cb4db7303a")
    (status available)
    (term
     (Bind
      ($r :: (Referents Entity))
      (Refer (λ (($named :: (Referents Entity))) (Named "alis" $named)))
      (Assert
       (Bind
        ($ctx2 :: (Referents Entity))
        (Context)
        ($ctx3 :: (Referents Entity))
        (Context)
        ($ctx4 :: (Referents Entity))
        (Context)
        ($ctx5 :: (Referents Entity))
        (Context)
        (CloseClause
         (λ (($actual_event :: (Referents Eventuality)))
           (∧
            ((λ (($event :: (Referents Eventuality))) (klama $r $ctx2 $ctx3 $ctx4 $ctx5 $event)) $actual_event)
            (fasnu $actual_event)))))))))
  (case (id "e69b9851e31ac7dae947e10cb7bd7ddeedeca790")
    (status available)
    (term
     (Bind
      ($r :: (Referents Entity))
      (Refer (λ (($unit :: (Referents Entity))) (mlatu $unit)))
      (Assert
       (Bind
        ($w :: (Referents Entity))
        (Presuppose
         (∃ (λ (($x :: Entity)) (gerku $x)))
         (Refer
          (λ (($reference :: (Referents Entity)))
            (∧
             (∧
              (∀ (λ (($member :: Entity)) (→ (Among $member $reference) ((λ (($x :: Entity)) (gerku $x)) $member))))
              (∀
               (λ (($subreference :: (Referents Entity)))
                 (→
                  (Among $subreference $reference)
                  (∃
                   (λ (($member :: Entity))
                     (∧
                      ((λ (($x :: Entity)) (gerku $x)) $member)
                      (∃
                       (λ (($common :: (Referents Entity)))
                         (∧ (Among $common $member) (Among $common $subreference)))))))))))
             (∀ (λ (($member :: Entity)) (→ ((λ (($x :: Entity)) (gerku $x)) $member) (Among $member $reference))))))))
        (∀
         (λ (($member :: Entity))
           (→
            (Among $member $w)
            ((λ (($x :: Entity))
               (Bind
                ($ctx3 :: (Referents Entity))
                (Context)
                (CloseClause
                 (λ (($actual_event :: (Referents Eventuality)))
                   (∧
                    ((λ (($event :: (Referents Eventuality))) (tavla $r $x $ctx3 $event)) $actual_event)
                    (fasnu $actual_event))))))
             $member)))))))))
  (case (id "e6de3a77f1ef095f2c747f051f659f74f57ebab3")
    (status available)
    (term
     (Bind
      ($o :: (ActOccurrence Assertion))
      (Local
       (Perform
        (Assert
         (CloseClause
          (λ (($actual_event :: (Referents Eventuality)))
            (∧ ((StateClause (gerku Speaker)) $actual_event) (fasnu $actual_event)))))))
      (Mention $o))))
  (case (id "e72922e2754b6fbae2733c861813fd899a07eb3a")
    (status unavailable)
    (reason "m2-oracle: Close has no adapter-supplied lexical row declaration"))
  (case (id "e97a3f27befc567d541ac57e93d47c88db3e5370")
    (status available)
    (term ((λ (($a :: (Act Assertion))) (Mention $a)) (Mention Speaker))))
  (case (id "ec2d5fbe1f794cd8f00cd46255188ca070b7f0c1")
    (status available)
    (term
     (Bind
      ($surface :: (Referents Entity))
      (Context)
      ($limbs :: (Referents Entity))
      (Context)
      ($gait :: (Referents Entity))
      (Context)
      (=
       (Card
        (SetOf
         (λ (($x :: Entity))
           (∧
            (gerku $x)
            (CloseClause
             (λ (($actual_event :: (Referents Eventuality)))
               (∧
                ((λ (($event :: (Referents Eventuality))) (bajra $x $surface $limbs $gait $event)) $actual_event)
                (fasnu $actual_event))))))))
       3))))
  (case (id "ef0d085f9a8c3af028bb48b3c99f40d636cb9385")
    (status available)
    (term
     (Bind
      ($r :: (Referents Entity))
      (Refer (λ (($named :: (Referents Entity))) (Named "alis" $named)))
      (Assert
       (Bind
        ($ctx3 :: (Referents Entity))
        (Context)
        (CloseClause
         (λ (($actual_event :: (Referents Eventuality)))
           (∧
            ((λ (($event :: (Referents Eventuality))) (tavla $r Speaker $ctx3 $event)) $actual_event)
            (fasnu $actual_event)))))))))
  (case (id "f653cb0a56774dea1f78c007c770b90d51c88371")
    (status available)
    (term
     ((λ (($a :: (Act Assertion))) (Do (Perform $a) (Perform $a)))
      (Assert
       (CloseClause
        (λ (($actual_event :: (Referents Eventuality)))
          (∧ ((StateClause (gerku Speaker)) $actual_event) (fasnu $actual_event))))))))
  (case (id "f695d47c0ad2f542eae100e0b6815df434e79933")
    (status available)
    (term
     (Assert
      (Presuppose
       (∃
        (λ (($x :: Entity))
          (∧
           (prenu $x)
           (∃
            (λ (($y :: Entity))
              (∧
               (xasli $y)
               (CloseClause
                (λ (($actual_event :: (Referents Eventuality)))
                  (∧ ((StateClause (ponse $x $y)) $actual_event) (fasnu $actual_event))))))))))
       (∀
        (λ (($p :: Entity) ($d :: (Referents Entity)))
          (→
           (∧
            (prenu $p)
            (∀ (λ (($member :: Entity)) (→ (Among $member $d) ((λ (($z :: Entity)) (xasli $z)) $member))))
            (CloseClause
             (λ (($actual_event :: (Referents Eventuality)))
               (∧ ((StateClause (ponse $p $d)) $actual_event) (fasnu $actual_event)))))
           (Bind
            ($ctx3 :: (Referents Entity))
            (Context)
            (CloseClause
             (λ (($actual_event :: (Referents Eventuality)))
               (∧
                ((λ (($event :: (Referents Eventuality))) (darxi $p $d $ctx3 $event)) $actual_event)
                (fasnu $actual_event))))))))))))
  (case (id "f9f7acbbeb94b894a71e501a3ec02e82877fd496")
    (status available)
    (term
     (Assert
      (Bind
       ($w1 :: (Referents Entity))
       (SelectAtLeast 1 (λ (($x :: Entity)) (gerku $x)))
       ((λ (($w :: (Referents Entity)))
          (Bind
           ($ctx3 :: (Referents Entity))
           (Context)
           (CloseClause
            (λ (($actual_event :: (Referents Eventuality)))
              (∧
               ((λ (($event :: (Referents Eventuality))) (tavla Speaker $w $ctx3 $event)) $actual_event)
               (fasnu $actual_event))))))
        $w1)))))
  (case (id "fb5015ae6fdfa682c9b7f70814a49daf00df1d91")
    (status available)
    (term
     (SetOf
      (λ (($z :: Entity))
        (Bind
         ($w1 :: (Referents Entity))
         (SelectExactly 1 (λ (($x :: Entity)) (gerku $x)))
         ((λ (($w :: (Referents Entity)))
            (CloseClause
             (λ (($actual_event :: (Referents Eventuality)))
               (∧ ((λ (($event :: (Referents Eventuality))) (jmaji $w $event)) $actual_event) (fasnu $actual_event)))))
          $w1))))))
  (case (id "fdcc4eabea6f2fa114a1eef0cb43fcc0aa653e60")
    (status unavailable)
    (reason
     "a0-expand-close: (a0-expand-close (row jinvi 4 holding-state (1 2 3 4)) ((1 Speaker) (2 (Reify (Let ($p Proposition) (Reify (CloseWith (row klama 5 direct-event (1 2 3 4 5)) ((1 Audience)))) (Supplement $p (Close (EvidentialBasis Speaker $p Hearsay)) (Holds $p))))))) is not in my domain"))
  (case (id "fe81c08b40808760d2268088eb37bd2e0a092ad2")
    (status unavailable)
    (reason
     "b1-expand-at-least: (b1-expand-at-least 0 Entity (λ (($x Entity)) (gerku $x)) (λ (($w (Referents Entity))) (Bind (($s Scale (Context))) (CloseWith (row jmaji 1 direct-event (1)) ((1 $w)))))) is not in my domain"))
  (case (id "ff0589096c5b179be217803445eae85e2e574fdc")
    (status unavailable)
    (reason
     "a0-expand-exactly: (a0-expand-exactly 1 Entity (λ (($x Entity)) (Bind (($s Scale (Context))) (gerku $x))) (λ (($w (Referents Entity))) (CloseWith (row jmaji 1 direct-event (1)) ((1 $w))))) is not in my domain"))))
