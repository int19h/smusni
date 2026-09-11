(smusni-m2-redex-oracle
 1
 (count 192)
 (cases
  (case (id "00f285c20c1d4c97eb6bcbc5cdb7326f5ddebe9c")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Assert (PluralNo (λ (($r (Referents Entity))) (gerku $r)) (λ (($w (Referents Entity))) (CloseWith (row tavla 3 direct-event (1 2 3)) ((1 Speaker) (2 $w))))))"))
  (case (id "01e7d0c79ab6dcf6fefc887563acc054518095c7")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Bind (($cat (Referents Entity) (Refer (λ (($x (Referents Entity))) (∧ (mlatu $x) (blabi $x)))))) (Assert (CloseWith (row jbena 3 direct-event (1 2 3)) ((1 $cat)))))"))
  (case (id "0298272aa8ac278e5f0f71e73a81ae56463248da")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Mention (IndividualSome (λ (($x Entity)) (gerku $x)) (λ (($w Entity)) (CloseWith (row tavla 3 direct-event (1 2 3)) ((1 $w) (2 Speaker))))))"))
  (case (id "0361b7fdaa1fd90b87b97a7934892d93cf982dcd")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Every (λ (($x Entity)) (gerku $x)) (λ (($w (Referents Entity))) (CloseWith (row jmaji 1 direct-event (1)) ((1 $w)))))"))
  (case (id "038b8fcbab5676b23e7c9404352cb5726b47a3f4")
    (status unavailable)
    (reason
     "outside frozen A0 source grammar: '(Assert (∀ (λ (($p Entity) ($d Entity)) (→ (∧ (prenu $p) (xasli $d) (CloseWith (row ponse 2 holding-state (1 2)) ((1 $p) (2 $d)))) (CloseWith (row darxi 3 direct-event (1 2 3)) ((1 $p) (2 $d)))))))"))
  (case (id "068cb85ec8ecb3ccc509a1792f79f631c2f91654")
    (status available)
    (source-type Content)
    (term
     (∧
      ((λ (($left :: (Referents Entity)) ($right :: (Referents Entity)))
         (CloseClause
          (λ (($actual_event :: (Referents Eventuality)))
            (∧
             ((λ (($event :: (Referents Eventuality)))
                (Bind ($ctx3 :: (Referents Entity)) (Context) (tavla $left $right $ctx3 $event)))
              $actual_event)
             (fasnu $actual_event)))))
       Speaker
       Audience)
      (∧
       ((λ (($left :: (Referents Entity)) ($right :: (Referents Entity)))
          (CloseClause
           (λ (($actual_event :: (Referents Eventuality)))
             (∧
              ((λ (($event :: (Referents Eventuality)))
                 (Bind ($ctx3 :: (Referents Entity)) (Context) (tavla $left $right $ctx3 $event)))
               $actual_event)
              (fasnu $actual_event)))))
        Audience
        Speaker)
       (∧)))))
  (case (id "06f586c55e74376156ae79cd85dda5169a1e02ef")
    (status available)
    (source-type Content)
    (term (∃ (λ (($r1 :: (Referents Entity))) (∧ ($x $r1) ($r $r1))))))
  (case (id "078157eb65184191ef0b23c478b1f6ef49ce5b5a")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Assert (CloseWith (row remna 1 holding-state (1)) ((1 (Combine Speaker Audience)))))"))
  (case (id "08eddca2756cf8f0c81d55982e8bc825d85ca200")
    (status unavailable)
    (reason
     "outside frozen A0 source grammar: '(Let ($prior (Act Assertion)) (Assert (CloseWith (row klama 5 direct-event (1 2 3 4 5)) ((1 Audience)))) (Bind (($prioro (ActOccurrence Assertion) (Perform Host $prior))) (Bind (($defect DefectKind (Context))) (Express (Close (MetalinguisticallyDefecti..."))
  (case (id "0ae10fc13e1a3271b1c51c7a1f0c877736111c75")
    (status available)
    (source-type Content)
    (term (¬ (∃ (λ (($x1 :: Entity)) (∧ ($x $x1) ($r $x1)))))))
  (case (id "0d601ed905f846a1cd7cf233d21969f42dcafb9c")
    (status available)
    (source-type Content)
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
  (case (id "10e172fe2b4ae74dcee850b13b1f74c32a0743ca")
    (status unavailable)
    (reason
     "outside frozen A0 source grammar: '(FewerThan 1 (λ (($x Entity)) (Bind (($s Scale (Context))) (gerku $x))) (λ (($w (Referents Entity))) (CloseWith (row jmaji 1 direct-event (1)) ((1 $w)))))"))
  (case (id "163f9eb77e8852c86feb74b030f5c1347945843d")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Bind (($r (Referents Entity) (Refer (λ (($unit1 (Referents Entity))) (gerku $unit1))))) (Bind (($r1 (Referents Entity) (Refer (λ (($unit (Referents Entity))) (gerku $unit))))) (Assert (CloseWith (row tavla 3 direct-event (1 2 3)) ((1 $r) (2 $r1))))))"))
  (case (id "1a3f5fdf1ea9c89e3c5f501e40925679e903b085")
    (status unavailable)
    (reason
     "outside frozen A0 source grammar: '(AtLeast 1 (λ (($x Entity)) (Bind (($s Scale (Context))) (gerku $x))) (λ (($w (Referents Entity))) (CloseWith (row jmaji 1 direct-event (1)) ((1 $w)))))"))
  (case (id "1a4e6e5501397b319459f53492a14a0f5876ad5b")
    (status available)
    (source-type Content)
    (term (¬ (∃ (λ (($r1 :: (Referents Entity))) (∧ ($x $r1) ($r $r1)))))))
  (case (id "1ae8d66b81c220f5f975851d5f78bfa701a2156a")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(SetOf (λ (($z Entity)) (Exactly 1 (λ (($x Entity)) (gerku $x)) (λ (($w (Referents Entity))) (CloseWith (row jmaji 1 direct-event (1)) ((1 $w)))))))"))
  (case (id "1c2ab7c93bcd012ac149f040ac9d6b01090ab999")
    (status available)
    (source-type Content)
    (term
     (∃
      (λ (($x1 :: Entity))
        (∧
         ((λ (($x :: Entity)) (gerku $x)) $x1)
         ((λ (($w :: Entity))
            (CloseClause
             (λ (($actual_event :: (Referents Eventuality)))
               (∧
                ((λ (($event :: (Referents Eventuality)))
                   (Bind ($ctx3 :: (Referents Entity)) (Context) (tavla $w Speaker $ctx3 $event)))
                 $actual_event)
                (fasnu $actual_event)))))
          $x1))))))
  (case (id "1c584ece802cf5eeeb22e0806f65553d4ce57751")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Bind (($dogs (Referents Entity) (SelectExactly 3 (λ (($x Entity)) (gerku $x))))) (Do (Assert (CloseWith (row bajra 4 direct-event (1 2 3 4)) ((1 $dogs)))) (Assert (CloseWith (row tatpi 1 holding-state (1)) ((1 $dogs))))))"))
  (case (id "1cdeb2331917ac3fc16b0059367689396360d1bd")
    (status available)
    (source-type (Fn ((Fn (Entity) Content) (Referents Entity)) Content))
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
  (case (id "1de177f660bc3c934b18cd20087636c6dce7f837")
    (status available)
    (source-type (Set Entity))
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
  (case (id "1f230961b78eba4c32fa85357a53872d5f42e8b2")
    (status available)
    (source-type Content)
    (term (∃ (λ (($r1 :: (Referents Eventuality))) (∧ ($x $r1) ($r $r1))))))
  (case (id "1faa3d381d7a55a274d312d2b4440b20c7a83fbc")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Bind (($r (Referents Entity) (Refer (λ (($unit1 (Referents Entity))) (gerku $unit1))))) (Bind (($r1 (Referents Entity) (Refer (λ (($unit (Referents Entity))) (mlatu $unit))))) (Assert (CloseWith (row tavla 3 direct-event (1 2 3)) ((1 $r) (2 $r1))))))"))
  (case (id "225e7d353ded74a470710a349dcda7f28dc1521f")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Assert (≤ (Card (SetOf (λ (($individual Entity)) (∧ (gerku $individual) (CloseWith (row blabi 1 holding-state (1)) ((1 $individual))))))) 1))"))
  (case (id "228ea135aca439f8a9037357f905d482636fa1c2")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(λ (($p (Fn (Eventuality) Content)) ($r (Referents Entity))) (CoveredBy $p $r))"))
  (case (id "2297a9f1838329374a54c08b2bc3b139383cc675")
    (status unavailable)
    (reason
     "outside frozen A0 source grammar: '(Bind (($alis (Referents Entity) (Refer (λ (($x (Referents Entity))) (Named \"alis\" $x))))) (Assert (CloseWith (row klama 5 direct-event (1 2 3 4 5)) ((1 $alis)))))"))
  (case (id "26621cc9a7405cfc3f9153a08e71bb0278b96fdd")
    (status available)
    (source-type Content)
    (term (∀ (λ (($x1 :: Number)) (→ ($x $x1) ($r $x1))))))
  (case (id "2674c959b1316b976f7fd51ff62e90f4720aa8c4")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Assert (CloseWith (row klama 5 direct-event (1 2 3 4 5)) ((1 Speaker))))"))
  (case (id "2ae03060ef75f54562b55d53c50ed510111e4d71")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Bind (($restrictor_klama_2 (Referents Entity) (Context)) ($restrictor_klama_3 (Referents Entity) (Context)) ($restrictor_klama_4 (Referents Entity) (Context)) ($restrictor_klama_5 (Referents Entity) (Context)) ($nuclear_tavla_3 (Referents Entity) (Con..."))
  (case (id "2df594eb652eeff97414edc08a6c3b6dd3362aa6")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(SentenceSign (CloseWith (row gerku 1 holding-state (1)) ((1 Speaker))))"))
  (case (id "2e201b96a49b39319af3a98efa71e286ae4c1742")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Assert (GlobalExactly 3 (λ (($restrictor_member Entity)) (gerku $restrictor_member)) (λ (($nuclear_member Entity)) (CloseWith (row blabi 1 holding-state (1)) ((1 $nuclear_member))))))"))
  (case (id "2f4f686f45b42fd8c7f3977c7f22f3fc2159a7eb")
    (status available)
    (source-type Content)
    (term (∃ (λ (($r1 :: (Referents Number))) (∧ ($x $r1) ($r $r1))))))
  (case (id "2f6f72b4075986be93027f581ec3ff9a40467c58")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Assert (IndividualEvery (λ (($x Entity)) (gerku $x)) (λ (($x Entity)) (Bind (($nuclear_tavla_3 (Referents Entity) (Context))) (GlobalExactly 3 (λ (($restrictor_member Entity)) (mlatu $restrictor_member)) (λ (($nuclear_member Entity)) (CloseWith (row t..."))
  (case (id "2fa405b6aa500b4c03e7851595792fca30324da2")
    (status available)
    (source-type Content)
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
  (case (id "30d2975027dd33918e02066cc068654abe8594a7")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Bind (($r (Referents Entity) (Refer (λ (($unit (Referents Entity))) (gerku $unit))))) (Assert (CloseWith (row blabi 1 holding-state (1)) ((1 $r)))))"))
  (case (id "3306bf521fa1bc3710990343bc13d0ab345caaa8")
    (status unavailable)
    (reason
     "outside frozen A0 source grammar: '(Some (λ (($x Entity)) (gerku $x)) (λ (($w (Referents Entity))) (Bind (($s Scale (Context))) (CloseWith (row jmaji 1 direct-event (1)) ((1 $w))))))"))
  (case (id "35098685acdf2649ac62f161849255287c79376d")
    (status available)
    (source-type Content)
    (term (¬ (∃ (λ (($r1 :: (Referents Eventuality))) (∧ ($x $r1) ($r $r1)))))))
  (case (id "37e0504b5a61407b1de93761e6cd8ed4e0bc15e9")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Let ($a (Act Assertion)) (Assert (CloseWith (row klama 5 direct-event (1 2 3 4 5)) ((1 Speaker)))) (Do (Perform $a) (Perform $a)))"))
  (case (id "3800c312509274326019e9d34421c1bb5c948ffb")
    (status unavailable)
    (reason
     "outside frozen A0 source grammar: '(Let ($a (Act Assertion)) (Assert (CloseWith (row klama 5 direct-event (1 2 3 4 5)) ((1 Audience)))) (Bind (($o (ActOccurrence Assertion) (Perform Host $a))) (Do (Perform AttachedDisplay (Express (Close (Happiness Speaker $o Moderate)))))))"))
  (case (id "3945ffc8a81358ba3de498b020e825ded20ae2fb")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Bind (($left (Referents Entity) (SelectExactly 3 (λ (($x Entity)) (gerku $x)))) ($right (Referents Entity) (SelectExactly 2 (λ (($x1 Entity)) (prenu $x1))))) (Mention (Distrib (λ (($l Entity)) (Distrib (λ (($r Entity)) (CloseWith (row nelci 2 holding-..."))
  (case (id "3c6e76459fb6e51496d660ddf53d065d17487511")
    (status available)
    (source-type Content)
    (term (∃ (λ (($x1 :: Eventuality)) (∧ ($x $x1) ($r $x1))))))
  (case (id "3d4c01783fbef8bf7c1aa4d914bd9373e6a92998")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Assert (IndividualEvery (λ (($person Entity)) (∧ (prenu $person) (IndividualSome (λ (($dog Entity)) (gerku $dog)) (λ (($dog Entity)) (CloseWith (row ponse 2 holding-state (1 2)) ((1 $person) (2 $dog))))))) (λ (($person Entity)) (CloseWith (row blabi 1..."))
  (case (id "3e382008dbd76314c637d4769638b692e5b543dc")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Mention (IndividualSome (λ (($x Entity)) (gerku $x)) (λ (($w Entity)) (CloseWith (row tavla 3 direct-event (1 2 3)) ((1 Speaker) (2 $w))))))"))
  (case (id "401b48e04fe0414f92ae23cce34be57bd8153108")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Bind (($r (Referents Entity) (Refer (λ (($unit2 (Referents Entity))) (prenu $unit2))))) (Bind (($r1 (Referents Entity) (Refer (λ (($unit1 (Referents Entity))) (gerku $unit1))))) (Bind (($r2 (Referents Entity) (Refer (λ (($unit (Referents Entity))) (ml..."))
  (case (id "40ad3544727c866dc86d6a3e10c48888773f3703")
    (status available)
    (source-type Content)
    (term (∃ (λ (($x1 :: Number)) (∧ ($x $x1) ($r $x1))))))
  (case (id "41639ddaaa12f66e8b6030f81fedc3c3f957080a")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(SetOf (λ (($z Entity)) (MoreThan 0 (λ (($x Entity)) (gerku $x)) (λ (($w (Referents Entity))) (CloseWith (row jmaji 1 direct-event (1)) ((1 $w)))))))"))
  (case (id "42512cb6c1feb1992c7275ad3b5e27a2aa828242")
    (status unavailable)
    (reason
     "outside frozen A0 source grammar: '(Bind (($r (Referents Entity) (Refer (λ (($named (Referents Entity))) (Named \"alis\" $named))))) (Assert (CloseWith (row tavla 3 direct-event (1 2 3)) ((1 $r) (2 Speaker)))))"))
  (case (id "4279b031e39014df46d1b9a3cfe6b6b5ad121e12")
    (status unavailable)
    (reason
     "outside frozen A0 source grammar: '(MoreThan 1 (λ (($x Entity)) (Bind (($s Scale (Context))) (gerku $x))) (λ (($w (Referents Entity))) (CloseWith (row jmaji 1 direct-event (1)) ((1 $w)))))"))
  (case (id "456266a00796914d921a0a47817fe86f7664cd19")
    (status available)
    (source-type Content)
    (term
     (∃
      (λ (($x1 :: Entity))
        (∧
         ((λ (($x :: Entity)) (gerku $x)) $x1)
         ((λ (($w :: Entity))
            (CloseClause
             (λ (($actual_event :: (Referents Eventuality)))
               (∧
                ((λ (($event :: (Referents Eventuality)))
                   (Bind ($ctx3 :: (Referents Entity)) (Context) (tavla Speaker $w $ctx3 $event)))
                 $actual_event)
                (fasnu $actual_event)))))
          $x1))))))
  (case (id "45fcd83ef1415d87f8822026b81b777d8debbca9")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Bind (($to (Referents Entity) (Context))) (Assert (CloseWith (row klama 5 direct-event (1 2 3 4 5)) ((1 (Combine Speaker Audience)) (2 $to)))))"))
  (case (id "46084d66c526ed3f7497ebad490c103b32621df4")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Assert (¬ (≤ 1 (Card (SetOf (λ (($individual Entity)) (∧ (gerku $individual) (CloseWith (row blabi 1 holding-state (1)) ((1 $individual))))))))))"))
  (case (id "4707e46c4d30caad4926e4549bbf0f7911abb47b")
    (status unavailable)
    (reason
     "outside frozen A0 source grammar: '(Bind (($kind (Referents Eventuality) (Refer (λ (($k (Referents Eventuality))) (fasnu $k))))) (Bind (($a (Referents AbstractNature) (Refer (λ (($x (Referents AbstractNature))) (Close ((SuhuRel (CloseWith (row klama 5 direct-event (1 2 3 4 5)) ((1 Speak..."))
  (case (id "499ca9118e3fa447ad93f6fd8674a7b4cf35db8e")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Bind (($r (Referents Entity) (Refer (λ (($unit (Referents Entity))) (mlatu $unit))))) (Bind (($nuclear_tavla_3 (Referents Entity) (Context))) (Assert (GlobalExactly 3 (λ (($restrictor_member Entity)) (gerku $restrictor_member)) (λ (($nuclear_member En..."))
  (case (id "4a46786294e9b949ea3e90effc906e344be6ac37")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Bind (($r (Referents Entity) (Refer (λ (($unit (Referents Entity))) (mlatu $unit))))) (Assert (PluralNo (λ (($r (Referents Entity))) (gerku $r)) (λ (($w (Referents Entity))) (CloseWith (row tavla 3 direct-event (1 2 3)) ((1 $r) (2 $w)))))))"))
  (case (id "4cf782da0ef70b9999054c6ba2dba51bdfec46ce")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Bind (($r (Referents Entity) (Refer (λ (($unit (Referents Entity))) (mlatu $unit))))) (Assert (PluralNo (λ (($r (Referents Entity))) (gerku $r)) (λ (($w (Referents Entity))) (CloseWith (row tavla 3 direct-event (1 2 3)) ((1 $w) (2 $r)))))))"))
  (case (id "5310a80dc550833859428eeb575349da99d34b2e")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Assert (PluralNo (λ (($r (Referents Entity))) (prenu $r)) (λ (($w (Referents Entity))) (CloseWith (row jmaji 1 direct-event (1)) ((1 $w))))))"))
  (case (id "56850bfe9375afc3abc8efd5fe19a85f6741e889")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Bind (($r (Referents Entity) (Refer (λ (($unit1 (Referents Entity))) (gerku $unit1))))) (Bind (($r1 (Referents Entity) (Refer (λ (($unit (Referents Entity))) (mlatu $unit))))) (Assert (CloseWith (row tavla 3 direct-event (1 2 3)) ((1 $r1) (2 $r))))))"))
  (case (id "569ded40de1611196c7100eaf0a94b84d2a5324d")
    (status available)
    (source-type Content)
    (term
     (∧
      ((λ (($s :: (Referents Entity)) ($l :: (Referents Entity)))
         (CloseClause
          (λ (($actual_event :: (Referents Eventuality)))
            (∧
             ((λ (($event :: (Referents Eventuality)))
                (Bind ($ctx3 :: (Referents Entity)) (Context) (tavla $s $l $ctx3 $event)))
              $actual_event)
             (fasnu $actual_event)))))
       Speaker
       Audience)
      (∧
       ((λ (($s :: (Referents Entity)) ($l :: (Referents Entity)))
          (CloseClause
           (λ (($actual_event :: (Referents Eventuality)))
             (∧
              ((λ (($event :: (Referents Eventuality)))
                 (Bind ($ctx3 :: (Referents Entity)) (Context) (tavla $s $l $ctx3 $event)))
               $actual_event)
              (fasnu $actual_event)))))
        Audience
        Speaker)
       (∧)))))
  (case (id "57a3f3b4bf979adb1958ec742ef08de24ea05dbb")
    (status unavailable)
    (reason "outside frozen A0 source grammar: '(λ (($p (PredTerm (RowOf zzzz)))) (Close $p))"))
  (case (id "584d2b9b8176244b8fb87599463e7d45ea325be0")
    (status available)
    (source-type Content)
    (term (∀ (λ (($x1 :: Eventuality)) (→ ($x $x1) ($r $x1))))))
  (case (id "58f295284d03c9933f8a15b05bfde1c7fafed92e")
    (status unavailable)
    (reason
     "outside frozen A0 source grammar: '(Some (λ (($x Entity)) (Bind (($s Scale (Context))) (gerku $x))) (λ (($w (Referents Entity))) (CloseWith (row jmaji 1 direct-event (1)) ((1 $w)))))"))
  (case (id "5b8f50f94ab9c5cf73e6c63c620a2da5e577d645")
    (status unavailable)
    (reason
     "outside frozen A0 source grammar: '(Let ($a (Act Assertion)) (Assert (CloseWith (row klama 5 direct-event (1 2 3 4 5)) ((1 Speaker)))) (Bind (($o (ActOccurrence Assertion) (Perform Host $a))) (Do (Perform AttachedDisplay (Express (Close (Happiness Speaker $o Moderate)))))))"))
  (case (id "5c28920f4680f966965e1bc31c49f52f686d9f14")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Assert (≤ 2 (Card (SetOf (λ (($individual Entity)) (∧ (gerku $individual) (CloseWith (row blabi 1 holding-state (1)) ((1 $individual)))))))))"))
  (case (id "5c4fa3efcb05afef484334fd42f97c7dc3836742")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Bind (($r (Referents Entity) (Refer (λ (($unit (Referents Entity))) (mlatu $unit))))) (Assert (IndividualSome (λ (($x Entity)) (gerku $x)) (λ (($w Entity)) (CloseWith (row tavla 3 direct-event (1 2 3)) ((1 $w) (2 $r)))))))"))
  (case (id "5d5e9465192f02b7a9c6e6adc49a3511886fe6cc")
    (status available)
    (source-type (Fn ((Referents Entity) (Fn (Entity) Content)) Content))
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
  (case (id "5e733e8cd5911c7c96c6a824e4d9a6fc430ebea9")
    (status available)
    (source-type Content)
    (term (¬ (∃ (λ (($x1 :: Number)) (∧ ($x $x1) ($r $x1)))))))
  (case (id "5e83d7a5f51758bf22dc589083fa84ef44b2d2ae")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Bind (($r (Referents Entity) (Refer (λ (($unit (Referents Entity))) (mlatu $unit))))) (Assert (CloseWith (row blabi 1 holding-state (1)) ((1 $r)))))"))
  (case (id "609a723c6e01ff803d936b0a5dabaa91fdcddc8f")
    (status unavailable)
    (reason
     "outside frozen A0 source grammar: '(Bind (($bob (Referents Entity) (Refer (λ (($x (Referents Entity))) (Named \"bab\" $x))))) (Do (Assert (CloseWith (row klama 5 direct-event (1 2 3 4 5)) ((1 $bob)))) (Assert (CloseWith (row prami 2 holding-state (1 2)) ((1 $bob))))))"))
  (case (id "613827a28e0a41ef129ee1be93f65a68ebf9cf80")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Assert (CloseWith (row jmaji 1 direct-event (1)) ((1 (Combine Speaker Audience)))))"))
  (case (id "63f5f18694818117743c94ef567a0a25cc148c8d")
    (status available)
    (source-type (Set Entity))
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
  (case (id "65325e3e4bef79ef24aae7f433ccdfbc1631068a")
    (status unavailable)
    (reason
     "outside frozen A0 source grammar: '(Let ($a (Act Assertion)) (Assert (CloseWith (row klama 5 direct-event (1 2 3 4 5)) ((1 Audience)))) (Bind (($o (ActOccurrence Assertion) (Perform Host $a))) (Do (Perform AttachedDisplay (Express (Close (Unhappiness Speaker $o Intense)))))))"))
  (case (id "664df3e8556e0a62f97819ff67a3f97ddf3d2fbb")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Assert (IndividualEvery (λ (($x Entity)) (gerku $x)) (λ (($dog Entity)) (Bind (($cats (Referents Entity) (Refer (λ (($r (Referents Entity))) (mlatu $r))))) (CloseWith (row tavla 3 direct-event (1 2 3)) ((1 $dog) (2 $cats)))))))"))
  (case (id "67ff470133d903644f177769fbc5561854e7e6dc")
    (status unavailable)
    (reason
     "outside frozen A0 source grammar: '(Bind (($n Natural (Vague (AdmissibleThreshold ManyK (λ (($x Entity)) (prenu $x)))))) (Assert (AtLeast $n (λ (($x Entity)) (prenu $x)) (λ (($w (Referents Entity))) (CloseWith (row klama 5 direct-event (1 2 3 4 5)) ((1 $w)))))))"))
  (case (id "688ba4db95ac4d4b239dd48568fd2fc0181f4e21")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Assert (IndividualEvery (λ (($x Entity)) (gerku $x)) (λ (($dog Entity)) (IndividualSome (λ (($y Entity)) (mlatu $y)) (λ (($cat Entity)) (CloseWith (row tavla 3 direct-event (1 2 3)) ((1 $dog) (2 $cat))))))))"))
  (case (id "6a043d6309c1781f3ebb6498a04b58eb4c803ab2")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(λ (($k (DecompositionBasis (Group Entity) Entity))) (Bind (($g (Referents (Group Entity)) (Massify $k Speaker))) (Mention $g)))"))
  (case (id "6abf77640d191b879fe6dd6ee20495fe92cb184c")
    (status available)
    (source-type Content)
    (term (¬ (∃ (λ (($r1 :: (Referents Number))) (∧ ($x $r1) ($r $r1)))))))
  (case (id "6b6a74d53949b42f13a305eb8a433ff35b1306e1")
    (status available)
    (source-type Content)
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
  (case (id "6b7cd4795ca590f2940d074bdd8b2f97572670dc")
    (status available)
    (source-type Content)
    (term (∃ (λ (($x1 :: Entity)) (∧ ($x $x1) ($r $x1))))))
  (case (id "6c09f8d93e046865894afbb3f3c1929a429f40ab")
    (status available)
    (source-type Content)
    (term (∀ (λ (($x1 :: Entity)) (→ ($x $x1) ($r $x1))))))
  (case (id "6c7e4991a958113de57aecb1f41e4f78d5edb10b")
    (status unavailable)
    (reason
     "outside frozen A0 source grammar: '(FewerThan 1 (λ (($x Entity)) (gerku $x)) (λ (($w (Referents Entity))) (Bind (($s Scale (Context))) (CloseWith (row jmaji 1 direct-event (1)) ((1 $w))))))"))
  (case (id "6d4269259fb6b242a09098db55f5081796fcd4a4")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Assert (IndividualSome (λ (($x Entity)) (gerku $x)) (λ (($w Entity)) (CloseWith (row blabi 1 holding-state (1)) ((1 $w))))))"))
  (case (id "6d4b6f744f5602a81df7b29ecb1ae8b85c712d46")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Assert (Generic Typical (λ (($x Entity)) (mlatu $x)) (λ (($x Entity)) (CloseWith (row cinri 2 holding-state (1 2)) ((1 $x))))))"))
  (case (id "6db1c4b791f0854fe7956e9eaa47adf625c5027d")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(SetOf (λ (($z Entity)) (Some (λ (($x Entity)) (gerku $x)) (λ (($w (Referents Entity))) (CloseWith (row jmaji 1 direct-event (1)) ((1 $w)))))))"))
  (case (id "728f0d3f41d5d72fac367555d0c675c48620c6b2")
    (status available)
    (source-type Content)
    (term (∃ (λ (($x1 :: Number)) (∧ ($x $x1) ($r $x1))))))
  (case (id "72fb3cb79181a1791be16f47a654afc00f904d37")
    (status unavailable)
    (reason
     "outside frozen A0 source grammar: '(Let ($a1 (Act Assertion)) (Assert (CloseWith (row klama 5 direct-event (1 2 3 4 5)) ((1 Speaker)))) (Bind (($o1 (ActOccurrence Assertion) (Perform Host $a1))) (Let ($a2 (Act Assertion)) (Assert (CloseWith (row stali 1 direct-event (1)) ((1 Audience)))..."))
  (case (id "7347f150d8d6766f2f9f63d09617b3c25bc4430b")
    (status unavailable)
    (reason
     "outside frozen A0 source grammar: '(Generic Typical (λ (($x Entity)) (Bind (($s Scale (Context))) (gerku $x))) (λ (($x Entity)) (CloseWith (row jmaji 1 direct-event (1)) ((1 $x)))))"))
  (case (id "74a417577427efd188fd6769f54813962d552da7")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Mention (λ (($x (Referents Entity))) (CloseWith (row klama 5 direct-event (1 2 3 4 5)) ((2 $x)))))"))
  (case (id "797ad849c1240e52d6b5505f215c77aaafb5e3a2")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Combine Speaker (CloseWith (row gerku 1 holding-state (1)) ((1 Speaker))))"))
  (case (id "79f753ce71d86adc8a504da89297f9a3bf973028")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(SetOf (λ (($z Entity)) (AtLeast 1 (λ (($x Entity)) (gerku $x)) (λ (($w (Referents Entity))) (CloseWith (row jmaji 1 direct-event (1)) ((1 $w)))))))"))
  (case (id "7aa2e6942653e073da8cf8eef66f12c87be59028")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Ask (OpenQ (λ (($x (Referents Entity))) (CloseWith (row klama 5 direct-event (1 2 3 4 5)) ((1 $x))))))"))
  (case (id "7b1d5e60e23f16d48067b556539b444b6b936ff7")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Bind (($r (Referents Entity) (Refer (λ (($unit (Referents Entity))) (gerku $unit))))) (Assert (CloseWith (row tavla 3 direct-event (1 2 3)) ((1 $r) (2 Speaker)))))"))
  (case (id "7c8f2f67bf1093f2628eb0b721c214f13be28d20")
    (status available)
    (source-type Content)
    (term (∃ (λ (($r1 :: (Referents Entity))) (∧ ($x $r1) ($r $r1))))))
  (case (id "8063565f8a490905803bc6c8fff99697f49d2702")
    (status available)
    (source-type Content)
    (term (¬ (∃ (λ (($r1 :: (Referents Eventuality))) (∧ ($x $r1) ($r $r1)))))))
  (case (id "807d60a1b251490207d2b0419efe76156ba3ce3e")
    (status unavailable)
    (reason
     "outside frozen A0 source grammar: '(SetOf (λ (($z Entity)) (Exactly 0 (λ (($x Entity)) (gerku $x)) (λ (($w (Referents Entity))) (Bind (($s Scale (Context))) (CloseWith (row jmaji 1 direct-event (1)) ((1 $w))))))))"))
  (case (id "8195a6c9965e94753ece460fc0b472ef955eaa36")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Assert (PluralNo (λ (($r (Referents Entity))) (gerku $r)) (λ (($w (Referents Entity))) (CloseWith (row tavla 3 direct-event (1 2 3)) ((1 $w) (2 Speaker))))))"))
  (case (id "83c28a399ba2d060a09394adff67de5b8251d810")
    (status unavailable)
    (reason
     "outside frozen A0 source grammar: '(GlobalExactly 1 (λ (($x Entity)) (gerku $x)) (λ (($x Entity)) (Bind (($s Scale (Context))) (CloseWith (row jmaji 1 direct-event (1)) ((1 $x))))))"))
  (case (id "8469afa019d92a7909049b50368f82d82e314825")
    (status unavailable)
    (reason
     "outside frozen A0 source grammar: '(Bind (($r (PredTerm (Row (1 (Referents Entity)) (2 (Referents Entity)))) (Context))) (Assert (Close ($r Speaker Audience))))"))
  (case (id "886e105400c86d6f1a5b22877e21662be739caf3")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Bind (($cats (Referents Entity) (Refer (λ (($x (Referents Entity))) (mlatu $x))))) (Assert (IndividualEvery (λ (($x Entity)) (gerku $x)) (λ (($dog Entity)) (CloseWith (row tavla 3 direct-event (1 2 3)) ((1 $dog) (2 $cats)))))))"))
  (case (id "893d4618f7c9e82d98d5ac9467976c4026dcde0d")
    (status unavailable)
    (reason
     "outside frozen A0 source grammar: '(GlobalExactly 1 (λ (($x Entity)) (Bind (($s Scale (Context))) (gerku $x))) (λ (($x Entity)) (CloseWith (row jmaji 1 direct-event (1)) ((1 $x)))))"))
  (case (id "899e766795f1120c2768faedab8df28da6dcc76a")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Assert (¬ (IndividualEvery (λ (($restrictor_member Entity)) (gerku $restrictor_member)) (λ (($nuclear_member Entity)) (CloseWith (row blabi 1 holding-state (1)) ((1 $nuclear_member)))))))"))
  (case (id "8b86e0d58a4e8af2aa93b9c1f2873d53f0a5be4d")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Assert (IndividualEvery (λ (($x Entity)) (gerku $x)) (λ (($x Entity)) (IndividualSome (λ (($x Entity)) (mlatu $x)) (λ (($w Entity)) (CloseWith (row tavla 3 direct-event (1 2 3)) ((1 $x) (2 $w))))))))"))
  (case (id "8bbacf2e3a9cb171e3d8b04c3009595b354491bd")
    (status unavailable)
    (reason
     "outside frozen A0 source grammar: '(AtLeast 1 (λ (($x Entity)) (gerku $x)) (λ (($w (Referents Entity))) (Bind (($s Scale (Context))) (CloseWith (row jmaji 1 direct-event (1)) ((1 $w))))))"))
  (case (id "8de4c5f85e68470abc96866823afd74f3e074775")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Assert (IndividualEvery (λ (($x Entity)) (gerku $x)) (λ (($x Entity)) (CloseWith (row blabi 1 holding-state (1)) ((1 $x))))))"))
  (case (id "8ee5ad764ef5db64e852018b1434d359006e2ed9")
    (status available)
    (source-type Content)
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
  (case (id "9022041a57c37926cc637d38693ada4bf78a7777")
    (status available)
    (source-type Content)
    (term (¬ (∃ (λ (($x1 :: Eventuality)) (∧ ($x $x1) ($r $x1)))))))
  (case (id "9179373ca8c2e48ede6fe47086cebd79b7f61352")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(λ (($p (EFn (Entity) Content)) ($r (Referents Entity))) (CoveredBy $p $r))"))
  (case (id "927827bd0eb63e94871641a79be5e180d4ea708b")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Let ($a (Act Assertion)) (Assert (CloseWith (row gerku 1 holding-state (1)) ((1 Speaker)))) (Do (Perform $a) (Perform $a)))"))
  (case (id "92d4b7cb59345610a7003d6430c1d0cea49a3b3d")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Bind (($dogs (Referents Entity) (SelectExactly 3 (λ (($x Entity)) (gerku $x)))) ($people (Referents Entity) (SelectExactly 2 (λ (($x Entity)) (prenu $x))))) (Assert (Distrib (λ (($d Entity)) (Distrib (λ (($p Entity)) (CloseWith (row nelci 2 holding-st..."))
  (case (id "93343abb3be77f900c4f01056ef1b304a64a9617")
    (status unavailable)
    (reason
     "outside frozen A0 source grammar: '(Let ($a (Act Assertion)) (Assert (CloseWith (row cadzu 4 direct-event (1 2 3 4)) ((1 Audience)))) (Bind (($o (ActOccurrence Assertion) (Perform Host $a))) (Do (Perform AttachedDisplay (Express (Close (EvidentialBasis Speaker $o Observation)))))))"))
  (case (id "97357f261644577c1d46b7a290b77c7bba6036f3")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(λ (($k Number)) (Bind (($g (Referents (Group Entity)) (Massify $k Speaker))) (Mention $g)))"))
  (case (id "977660f15daa38c8411915d0adda06cb5a8d0840")
    (status unavailable)
    (reason
     "outside frozen A0 source grammar: '(No (λ (($x Entity)) (Bind (($s Scale (Context))) (gerku $x))) (λ (($w (Referents Entity))) (CloseWith (row jmaji 1 direct-event (1)) ((1 $w)))))"))
  (case (id "98277acc169bb0347d621f9493d0627322d73f09")
    (status available)
    (source-type Content)
    (term (∃ (λ (($x1 :: Entity)) (∧ ($x $x1) ($r $x1))))))
  (case (id "994764bf6b5e8953f65161d7013645dbd610834d")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Express (Close (Desire Speaker (Reify (CloseWith (row sipna 1 direct-event (1)) ((1 Speaker)))) Moderate)))"))
  (case (id "9a109bb39c927ec2d955da251ed7cac22d735f7b")
    (status available)
    (source-type Content)
    (term (∃ (λ (($r1 :: (Referents Number))) (∧ ($x $r1) ($r $r1))))))
  (case (id "9a5f9039e30a3c0f62c6dffe896447f940263dee")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Bind (($r (Referents Entity) (Refer (λ (($unit (Referents Entity))) (mlatu $unit))))) (Assert (IndividualEvery (λ (($x Entity)) (gerku $x)) (λ (($x Entity)) (CloseWith (row tavla 3 direct-event (1 2 3)) ((1 $r) (2 $x)))))))"))
  (case (id "9a980ead40a2b6ea97d8d541fb5902b8d38efe34")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Assert (¬ (IndividualEvery (λ (($x Entity)) (gerku $x)) (λ (($x Entity)) (CloseWith (row blabi 1 holding-state (1)) ((1 $x)))))))"))
  (case (id "9ae1fcf6b3c4296c14e99e6a239f7e14e3b14305")
    (status unavailable)
    (reason
     "outside frozen A0 source grammar: '(Bind (($w (Referents Entity) (SelectSome (λ (($x Entity)) (Bind (($s Scale (Context))) (gerku $x)))))) (Mention $w))"))
  (case (id "9b0069c6c532ffc53730fca1df4cbe883668cc96")
    (status unavailable)
    (reason
     "outside frozen A0 source grammar: '(Bind (($r (Referents Entity) (Refer (λ (($unit (Referents Entity))) (gerku $unit))))) (Bind (($r1 (Referents Entity) (Refer (λ (($named (Referents Entity))) (Named \"alis\" $named))))) (Assert (CloseWith (row tavla 3 direct-event (1 2 3)) ((1 $r) (2 $r1..."))
  (case (id "9d01bf3ff1a894bc21f6f52bbab08ecdac046100")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Bind (($w (Referents Entity) (SelectSome (λ (($x Entity)) (gerku $x))))) (Mention $w))"))
  (case (id "9e75541a32177df4862921c0a1e173badf2597d9")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Ask (Polar (CloseWith (row klama 5 direct-event (1 2 3 4 5)) ((1 Speaker)))))"))
  (case (id "9ff01861c7cef08a385d5748b306921770112a11")
    (status unavailable)
    (reason
     "outside frozen A0 source grammar: '(Exactly 1 (λ (($x Entity)) (gerku $x)) (λ (($w (Referents Entity))) (Bind (($s Scale (Context))) (CloseWith (row jmaji 1 direct-event (1)) ((1 $w))))))"))
  (case (id "a302c8338df5aad613878b9d502a427f75599292")
    (status available)
    (source-type Content)
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
  (case (id "a542c608466463f07a7ed0c98b750951ccd7c225")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Assert (¬ (≤ 1 (Card (SetOf (λ (($x Entity)) (∧ (gerku $x) (CloseWith (row blabi 1 holding-state (1)) ((1 $x))))))))))"))
  (case (id "a5b627375f35efc198d39b5a865d6de2b5ae61c5")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Bind (($r (Referents Entity) (Refer (λ (($unit1 (Referents Entity))) (mlatu $unit1))))) (Bind (($r1 (Referents Entity) (Refer (λ (($unit (Referents Entity))) (gerku $unit))))) (Assert (CloseWith (row klama 5 direct-event (1 2 3 4 5)) ((1 $r1) (3 $r))))))"))
  (case (id "a91759210f0b915f0ee06f4eb6011f93866bd93c")
    (status available)
    (source-type Content)
    (term (∀ (λ (($x1 :: Entity)) (→ ($x $x1) ($r $x1))))))
  (case (id "aa84ff3c8b6312ed818a899455117f59892ec52d")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Assert (GlobalExactly 1 (λ (($restrictor_member Entity)) (gerku $restrictor_member)) (λ (($individual Entity)) (¬ (CloseWith (row blabi 1 holding-state (1)) ((1 $individual)))))))"))
  (case (id "aa9e327b8b124c679e98ce58171b233532adf2d9")
    (status available)
    (source-type Content)
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
  (case (id "abff55d67e307c4c442096bbb892c482f083bae2")
    (status unavailable)
    (reason
     "outside frozen A0 source grammar: '(AtMost 1 (λ (($x Entity)) (gerku $x)) (λ (($w (Referents Entity))) (Bind (($s Scale (Context))) (CloseWith (row jmaji 1 direct-event (1)) ((1 $w))))))"))
  (case (id "aca8badfbc5ae8903bc68929e5d1c2390f1cf1fc")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Assert (¬ (≤ (Card (SetOf (λ (($individual Entity)) (∧ (gerku $individual) (CloseWith (row blabi 1 holding-state (1)) ((1 $individual))))))) 1)))"))
  (case (id "ad6d1c1cbff26a4a4cc7b92e1d26dd108d6c0cb0")
    (status unavailable)
    (reason "Refer-member-lift has ledger port-state none; term oracle unavailable"))
  (case (id "b12e3e06321a1d9c05fd3d5648a73688cb4dff9c")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Bind (($cat (Referents Entity) (Refer (λ (($x (Referents Entity))) (mlatu $x))))) (Assert (CloseWith (row blabi 1 holding-state (1)) ((1 $cat)))))"))
  (case (id "b1e2c2a9ab82f7f6d2d8cfca6a39b451ad8553c3")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Bind (($cat (Referents Entity) (Refer (λ (($x (Referents Entity))) (mlatu $x))))) (Do (Assert (CloseWith (row blabi 1 holding-state (1)) ((1 $cat)))) (Assert (CloseWith (row jbena 3 direct-event (1 2 3)) ((1 $cat))))))"))
  (case (id "b2501d03e5778a5466a75e9d99fbd0cf7ea1f273")
    (status available)
    (source-type Content)
    (term (∃ (λ (($x1 :: Eventuality)) (∧ ($x $x1) ($r $x1))))))
  (case (id "b2c08b72b4b178f52bc0e452a04465d14bfbdce1")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Bind (($left (Referents Entity) (SelectExactly 3 (λ (($x Entity)) (gerku $x)))) ($right (Referents Entity) (SelectExactly 2 (λ (($x1 Entity)) (prenu $x1))))) (Assert (Distrib (λ (($l Entity)) (Distrib (λ (($r Entity)) (CloseWith (row nelci 2 holding-s..."))
  (case (id "b4842086f1b7aca328d967227d306e69e18fbfdd")
    (status unavailable)
    (reason
     "outside frozen A0 source grammar: '(∀ (λ (($p Entity) ($d Entity)) (→ (∧ (prenu $p) (xasli $d) (CloseWith (row ponse 2 holding-state (1 2)) ((1 $p) (2 $d)))) (CloseWith (row darxi 3 direct-event (1 2 3)) ((1 $p) (2 $d))))))"))
  (case (id "b5b2cdded5db6db2f43a575b770cb7ca99fb9ea2")
    (status unavailable)
    (reason "source has 0 admitted A0 typings: '(Assert (CloseWith (row tavla 3 direct-event (1 2 3)) ((1 Speaker))))"))
  (case (id "b66d1b9582dc2ddf2e5204a1821cbf73c41dc96d")
    (status available)
    (source-type (EFn ((Referents Eventuality)) Content))
    (term
     (λ (($e :: (Referents Eventuality)))
       (CloseClause
        (λ (($clause_event :: (Referents Eventuality)))
          (∧
           (∧ (Among $clause_event $e) (Among $e $clause_event))
           ((λ (($actual_event :: (Referents Eventuality)))
              (∧
               ((λ (($lexical_event :: (Referents Eventuality)))
                  (Bind
                   ($ctx2 :: (Referents Entity))
                   (Context)
                   ($ctx3 :: (Referents Entity))
                   (Context)
                   ($ctx4 :: (Referents Entity))
                   (Context)
                   ($ctx5 :: (Referents Entity))
                   (Context)
                   (klama Speaker $ctx2 $ctx3 $ctx4 $ctx5 $lexical_event)))
                $actual_event)
               (fasnu $actual_event)))
            $e)))))))
  (case (id "b821a02c794ea3dae310afa75da8e693de0f6520")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Bind (($r (Referents Entity) (Refer (λ (($unit (Referents Entity))) (gerku $unit))))) (Assert (CloseWith (row tavla 3 direct-event (1 2 3)) ((1 Speaker) (2 $r)))))"))
  (case (id "ba57bd6a43e5bf1a1c30edd7d59243129da613b3")
    (status unavailable)
    (reason
     "outside frozen A0 source grammar: '(AtMost 1 (λ (($x Entity)) (Bind (($s Scale (Context))) (gerku $x))) (λ (($w (Referents Entity))) (CloseWith (row jmaji 1 direct-event (1)) ((1 $w)))))"))
  (case (id "ba8d386ae6848940b60f704e4629b05464b4c0b3")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Bind (($nuclear_bajra_2 (Referents Entity) (Context)) ($nuclear_bajra_3 (Referents Entity) (Context)) ($nuclear_bajra_4 (Referents Entity) (Context))) (Mention (GlobalExactly 3 (λ (($restrictor_member Entity)) (gerku $restrictor_member)) (λ (($nuclear..."))
  (case (id "bc109a29c300f54a9a026d5ca4701dbd96c8cd53")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Assert (IndividualNo (λ (($x Entity)) (gerku $x)) (λ (($w Entity)) (CloseWith (row blabi 1 holding-state (1)) ((1 $w))))))"))
  (case (id "bcff362502a0710daee4004eb9dcb572b5172cfb")
    (status available)
    (source-type (Set Entity))
    (term (SetOf (λ (($z :: Entity)) (∧)))))
  (case (id "bd4eef45e064c4737c1e0654f2707c154e3a1d4f")
    (status available)
    (source-type Content)
    (term (¬ (∃ (λ (($x1 :: Number)) (∧ ($x $x1) ($r $x1)))))))
  (case (id "bdd3d191b2cdc13f93625cd4ad2b8bfdcbc997f0")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(SetOf (λ (($z Entity)) (GlobalExactly 1 (λ (($x Entity)) (gerku $x)) (λ (($x Entity)) (CloseWith (row jmaji 1 direct-event (1)) ((1 $x)))))))"))
  (case (id "bfbea82538c52a0614b24010dbbfef6b97128d95")
    (status available)
    (source-type Content)
    (term
     (Bind
      ($w1 :: (Referents Entity))
      (SelectAtLeast 1 (λ (($x :: Entity)) (gerku $x)))
      ((λ (($w :: (Referents Entity)))
         (CloseClause
          (λ (($actual_event :: (Referents Eventuality)))
            (∧ ((λ (($event :: (Referents Eventuality))) (jmaji $w $event)) $actual_event) (fasnu $actual_event)))))
       $w1))))
  (case (id "c1c2b0ef79f5f36576e29b16620a3691c14c73d9")
    (status unavailable)
    (reason
     "outside frozen A0 source grammar: '(Bind (($a (Referents Amount) (Refer (λ (($x (Referents Amount))) (Close ((NiRel (CloseWith (row klama 5 direct-event (1 2 3 4 5)) ((1 Speaker)))) $x)))))) (Mention $a))"))
  (case (id "c224ce9bf417716f65f0929f616785a351c2cd3f")
    (status available)
    (source-type Content)
    (term (∃ (λ (($r1 :: (Referents Eventuality))) (∧ ($x $r1) ($r $r1))))))
  (case (id "c27edda4114ef35690169b876f3211f4d7c1555c")
    (status unavailable)
    (reason "source has 0 admitted A0 typings: '(Let ($a (Act Assertion)) (Mention Speaker) (Mention $a))"))
  (case (id "c34cc0743e85a8dd39494ac349a3c23c8929fd2e")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Assert (PluralNo (λ (($x (Referents Entity))) (prenu $x)) (λ (($w (Referents Entity))) (CloseWith (row jmaji 1 direct-event (1)) ((1 $w))))))"))
  (case (id "c3d5175b715643891982317b895cbad77bf79fed")
    (status available)
    (source-type (Set Entity))
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
  (case (id "c4debe5a04113791d00af097e623479a93f66c37")
    (status available)
    (source-type (EFn ((Referents Entity)) Content))
    (term
     (λ (($x :: (Referents Entity)))
       (CloseClause
        (λ (($actual_event :: (Referents Eventuality)))
          (∧
           ((λ (($event :: (Referents Eventuality)))
              (Bind
               ($ctx1 :: (Referents Entity))
               (Context)
               ($ctx3 :: (Referents Entity))
               (Context)
               ($ctx4 :: (Referents Entity))
               (Context)
               ($ctx5 :: (Referents Entity))
               (Context)
               (klama $ctx1 $x $ctx3 $ctx4 $ctx5 $event)))
            $actual_event)
           (fasnu $actual_event)))))))
  (case (id "c6df5810e743d1c33b69f3a07532317d8e8adcd8")
    (status available)
    (source-type Content)
    (term (¬ (∃ (λ (($r1 :: (Referents Entity))) (∧ ($x $r1) ($r $r1)))))))
  (case (id "c6fe437f0775a9c797d1d01aac783ed9f6b963cb")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Bind (($nuclear_bajra_2 (Referents Entity) (Context)) ($nuclear_bajra_3 (Referents Entity) (Context)) ($nuclear_bajra_4 (Referents Entity) (Context))) (Assert (GlobalExactly 3 (λ (($restrictor_member Entity)) (gerku $restrictor_member)) (λ (($nuclear_..."))
  (case (id "c8ca016b1559d11288d2c8b805e1d00131b759ae")
    (status available)
    (source-type Content)
    (term (∀ (λ (($x1 :: Eventuality)) (→ ($x $x1) ($r $x1))))))
  (case (id "c997a78089666f4b1d4c249f0894774dada51af1")
    (status unavailable)
    (reason
     "outside frozen A0 source grammar: '(Bind (($ep (Referents Epistemology) (Context))) (Bind (($tv (Referents TruthValue) (Refer (λ (($v (Referents TruthValue))) ((JeiRel (CloseWith (row klama 5 direct-event (1 2 3 4 5)) ((1 Speaker)))) $v $ep))))) (Mention $tv)))"))
  (case (id "ca3ded71dd1e695cfba61b2e74339866dbf5b8a7")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(SetOf (λ (($z Entity)) (Every (λ (($x Entity)) (gerku $x)) (λ (($x Entity)) (CloseWith (row jmaji 1 direct-event (1)) ((1 $x)))))))"))
  (case (id "cb59863b454b6e7a9a6795c1e2e0bea7bcc0153b")
    (status available)
    (source-type Content)
    (term
     (=
      (Card
       (SetOf
        (λ (($global_member :: Entity))
          (∧ ((λ (($p :: Entity)) (prenu $p)) $global_member) ((λ (($q :: Entity)) (blabi $q)) $global_member)))))
      2)))
  (case (id "ce45699d7eb9e11016049b21298002a2705d5d5c")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Bind (($r (Referents Entity) (Refer (λ (($unit (Referents Entity))) (mlatu $unit))))) (Bind (($nuclear_tavla_3 (Referents Entity) (Context))) (Assert (GlobalExactly 3 (λ (($restrictor_member Entity)) (gerku $restrictor_member)) (λ (($nuclear_member En..."))
  (case (id "d01eb068230f1e80e3c3ed7d9c796631ce69cc5f")
    (status unavailable)
    (reason
     "outside frozen A0 source grammar: '(MoreThan 1 (λ (($x Entity)) (gerku $x)) (λ (($w (Referents Entity))) (Bind (($s Scale (Context))) (CloseWith (row jmaji 1 direct-event (1)) ((1 $w))))))"))
  (case (id "d0cc53280e4d91b835ce82836376e405354417d1")
    (status available)
    (source-type Content)
    (term (¬ (∃ (λ (($x1 :: Entity)) (∧ ($x $x1) ($r $x1)))))))
  (case (id "d3cc2d63421b372fa9706846714eae4e84e0c92e")
    (status unavailable)
    (reason
     "outside frozen A0 source grammar: '(Bind (($r (PredTerm (Row (1 (Referents Entity)) (2 (Referents Entity)))) (Context))) (Mention (Close ($r Speaker Audience))))"))
  (case (id "d65220123db3801bf1df9efbe18153f04d2ece2d")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Assert (IndividualSome (λ (($x Entity)) (gerku $x)) (λ (($w Entity)) (CloseWith (row tavla 3 direct-event (1 2 3)) ((1 Speaker) (2 $w))))))"))
  (case (id "d8116f10e6b587310e323677fb87af53a97c9546")
    (status available)
    (source-type (Set Entity))
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
  (case (id "d8b36b937fefa5a941b54d815d584a63cb6b29bd")
    (status unavailable)
    (reason
     "outside frozen A0 source grammar: '(Bind (($r (Referents Entity) (Refer (λ (($named (Referents Entity))) (Named \"alis\" $named))))) (Assert (CloseWith (row klama 5 direct-event (1 2 3 4 5)) ((1 $r)))))"))
  (case (id "d924a1aa7f4bc1039efb2dd64206d0a1b24ff115")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Bind (($r (Referents Entity) (Refer (λ (($unit (Referents Entity))) (gerku $unit))))) (Mention (CloseWith (row tavla 3 direct-event (1 2 3)) ((1 Speaker) (2 $r)))))"))
  (case (id "d9df2233ecd2ee2c27d319998d42b84537e39553")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Mention (CloseWith (row klama 5 direct-event (1 2 3 4 5)) ((1 Speaker))))"))
  (case (id "dc12fd8dacfd4b1dfa96f655e71d7d9814fb582b")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Bind (($purpose (Referents Entity) (Context)) ($n Natural (Vague (AdmissibleThreshold TooManyK (λ (($x Entity)) (gerku $x)) $purpose)))) (Assert (MoreThan $n (λ (($x Entity)) (gerku $x)) (λ (($w (Referents Entity))) (CloseWith (row klama 5 direct-even..."))
  (case (id "dccf6a3cccec3ff3d46f75547336c59fe338009f")
    (status unavailable)
    (reason
     "outside frozen A0 source grammar: '(Every (λ (($x Entity)) (Bind (($s Scale (Context))) (gerku $x))) (λ (($x Entity)) (CloseWith (row jmaji 1 direct-event (1)) ((1 $x)))))"))
  (case (id "de705159d1bc8755c9a5d72c09869d9782f53df3")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(SentenceSign (Bind (($x Entity (Context))) (CloseWith (row klama 5 direct-event (1 2 3 4 5)) ((1 $x)))))"))
  (case (id "dfb4b58226460bc533a9327ff4b5ba4b038ce1a0")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Assert (IndividualSome (λ (($x Entity)) (gerku $x)) (λ (($w Entity)) (CloseWith (row tavla 3 direct-event (1 2 3)) ((1 $w) (2 Speaker))))))"))
  (case (id "e05cc572fd6b6b840840cd9fbbdbabd9e4e62950")
    (status unavailable)
    (reason
     "outside frozen A0 source grammar: '(Bind (($scale (Referents Scale) (Context))) (Bind (($amt (Referents Amount) (Refer (λ (($a (Referents Amount))) ((NiRel (CloseWith (row klama 5 direct-event (1 2 3 4 5)) ((1 Speaker)))) $a $scale))))) (Mention (− 1 (AmountValue $amt $scale)))))"))
  (case (id "e288e76dfd7af14ee2627dc6fc09e39e7f18a6e0")
    (status unavailable)
    (reason
     "outside frozen A0 source grammar: '(Assert (CloseWith (row jinvi 4 holding-state (1 2 3 4)) ((1 Speaker) (2 (Reify (Let ($p Proposition) (Reify (CloseWith (row klama 5 direct-event (1 2 3 4 5)) ((1 Audience)))) (Supplement $p (Close (EvidentialBasis Speaker $p Hearsay)) (Holds $p))))))))"))
  (case (id "e2ce0e1799ea8cf4c18d5b74d032a8994ba97f2d")
    (status unavailable)
    (reason
     "outside frozen A0 source grammar: '(Generic Typical (λ (($x Entity)) (gerku $x)) (λ (($x Entity)) (Bind (($s Scale (Context))) (CloseWith (row jmaji 1 direct-event (1)) ((1 $x))))))"))
  (case (id "e34ee1f435bac0f38afb4efe894e2f4e636f8354")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Assert (IndividualEvery (λ (($x Entity)) (gerku $x)) (λ (($x Entity)) (CloseWith (row tavla 3 direct-event (1 2 3)) ((1 Speaker) (2 $x))))))"))
  (case (id "e533292c6c297bc2c73568b993d2f258643b3cdf")
    (status available)
    (source-type Content)
    (term (∀ (λ (($x1 :: Number)) (→ ($x $x1) ($r $x1))))))
  (case (id "e61080c82b790cbb7d97bcf55133eade01154657")
    (status available)
    (source-type Content)
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
  (case (id "e7741842e2c111d58b9f8805ed75f7c87aa04aef")
    (status available)
    (source-type (EFn ((Fn (Eventuality) Content) ClauseContent) Content))
    (term
     (λ (($p :: (Fn (Eventuality) Content)) ($c :: ClauseContent))
       (Bind ($w :: (Referents Eventuality)) (SelectExactly 1 $p) ($c $w)))))
  (case (id "e7e8047acd858d3e76a63fb551fcf866ba531aa4")
    (status available)
    (source-type Content)
    (term (¬ (∃ (λ (($r1 :: (Referents Number))) (∧ ($x $r1) ($r $r1)))))))
  (case (id "e8b59917bcea981a6b70ee3821dd0a3176aeb930")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Bind (($r (Referents Entity) (Refer (λ (($unit (Referents Entity))) (mlatu $unit))))) (Assert (IndividualEvery (λ (($x Entity)) (gerku $x)) (λ (($x Entity)) (CloseWith (row tavla 3 direct-event (1 2 3)) ((1 $x) (2 $r)))))))"))
  (case (id "e8f9508e9d41a3a5a9382735368e6e0980471303")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Assert (GlobalExactly 25 (λ (($restrictor_member Entity)) (gerku $restrictor_member)) (λ (($nuclear_member Entity)) (CloseWith (row blabi 1 holding-state (1)) ((1 $nuclear_member))))))"))
  (case (id "ea11ee301fbff77623c9b012811e5f574f665074")
    (status unavailable)
    (reason
     "outside frozen A0 source grammar: '(Bind (($r (Referents Entity) (Refer (λ (($named (Referents Entity))) (Named \"alis\" $named))))) (Assert (CloseWith (row tavla 3 direct-event (1 2 3)) ((1 Speaker) (2 $r)))))"))
  (case (id "ed3d10bab935e3974118d4b5cc126cd56d9e5f60")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Bind (($o (ActOccurrence Assertion) (Local (Perform (Assert (CloseWith (row gerku 1 holding-state (1)) ((1 Speaker)))))))) (Mention $o))"))
  (case (id "ee4a39edab1a4e38533c3477cf23e58f4a9cb21f")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Bind (($r (Referents Entity) (Refer (λ (($unit (Referents Entity))) (mlatu $unit))))) (Assert (IndividualSome (λ (($x Entity)) (gerku $x)) (λ (($w Entity)) (CloseWith (row tavla 3 direct-event (1 2 3)) ((1 $r) (2 $w)))))))"))
  (case (id "f421ce619f4f1cebed311b7b93951081a5e3a6e6")
    (status unavailable)
    (reason
     "outside frozen A0 source grammar: '(Assert (CloseWith (row valsi 2 holding-state (1 2)) ((1 (WordSign \"klama\")))))"))
  (case (id "f7526f02968c2d0f940554bf7559692e5e9de6ea")
    (status available)
    (source-type Content)
    (term
     (Bind
      ($r :: (Referents Entity))
      (Refer (λ (($unit :: (Referents Entity))) (gerku $unit)))
      (CloseClause
       (λ (($actual_event :: (Referents Eventuality)))
         (∧
          ((λ (($event :: (Referents Eventuality)))
             (Bind ($ctx3 :: (Referents Entity)) (Context) (tavla Speaker $r $ctx3 $event)))
           $actual_event)
          (fasnu $actual_event)))))))
  (case (id "f7dad8b4f0992d634141ee234ec2fa08d7437659")
    (status unavailable)
    (reason
     "outside frozen A0 source grammar: '(SetOf (λ (($z Entity)) (AtLeast 0 (λ (($x Entity)) (gerku $x)) (λ (($w (Referents Entity))) (Bind (($s Scale (Context))) (CloseWith (row jmaji 1 direct-event (1)) ((1 $w))))))))"))
  (case (id "f83a3cb539fa4ffb35fd3404d7de53734705b247")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Assert (PluralNo (λ (($r (Referents Entity))) (mlatu $r)) (λ (($w (Referents Entity))) (CloseWith (row blabi 1 holding-state (1)) ((1 $w))))))"))
  (case (id "f9e7a3b9c2ff4e32c7bda88c9debc8c183a1c77e")
    (status unavailable)
    (reason
     "outside frozen A0 source grammar: '(No (λ (($x Entity)) (gerku $x)) (λ (($w (Referents Entity))) (Bind (($s Scale (Context))) (CloseWith (row jmaji 1 direct-event (1)) ((1 $w))))))"))
  (case (id "fb1e18d79b7a5c5c1f8a1d55d6cf15c664f717b4")
    (status unavailable)
    (reason
     "outside frozen A0 source grammar: '(Assert (∃ (λ (($dog Entity) ($person Entity)) (∧ (gerku $dog) (prenu $person) (CloseWith (row nelci 2 holding-state (1 2)) ((1 $dog) (2 $person)))))))"))
  (case (id "fb8f890ec4d851fb95e63bdb4520c30235ec48e1")
    (status available)
    (source-type Content)
    (term (¬ (∃ (λ (($x1 :: Eventuality)) (∧ ($x $x1) ($r $x1)))))))
  (case (id "fc68ab58b773d78fe0fa1fbb15ee3ac08fd02f9d")
    (status unavailable)
    (reason
     "outside frozen A0 source grammar: '(Exactly 1 (λ (($x Entity)) (Bind (($s Scale (Context))) (gerku $x))) (λ (($w (Referents Entity))) (CloseWith (row jmaji 1 direct-event (1)) ((1 $w)))))"))
  (case (id "fe4c9cd43ed9c80b57164c94ce440ae2326d0998")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(Bind (($nuclear_tavla_3 (Referents Entity) (Context))) (Assert (GlobalExactly 3 (λ (($restrictor_member Entity)) (gerku $restrictor_member)) (λ (($nuclear_member Entity)) (CloseWith (row tavla 3 direct-event (1 2 3)) ((1 Speaker) (2 $nuclear_member) (..."))
  (case (id "fecc256bfaacdc51a22517ddaf899499179207f8")
    (status unavailable)
    (reason
     "source has 0 admitted A0 typings: '(SetOf (λ (($x Entity)) (Bind (($r (Referents Entity) (SelectSome (λ (($y Entity)) (gerku $y))))) (gerku $x))))"))))
