(smusni-lowering-manifest 1
  ;; Candidate keys remain M1 fence keys. Ordered cases correspond to the
  ;; fence's top-level core forms; the surface is the Lojban portion of that
  ;; form's own leading comment. `#f` records a missing surface header.
  (fragment (families "L0" "L1" "L3" "L5") (lowering-judgments 46))

  (candidate "samples.md" 1 "738f3c4cc9a19d8708f73af84f65571286474905"
    (rules "L1.1" "L1.3" "L1.6")
    (case 1 "mi klama" sentence (promised-rows klama)))
  (candidate "samples.md" 3 "3db37afbd27c832ee661ef1fad0b621eb031fed6"
    (rules "L1.4" "L1.6")
    (case 1 "klama fe ti tu" sentence (promised-rows klama)))
  (candidate "samples.md" 4 "6ee5b8e402e2c2f6585d7ade3e4911d3faef1a2a"
    (rules "L1.5")
    (case 1 "mi klama ti zi'o ti ti" sentence (promised-rows klama)))
  (candidate "samples.md" 5 "bb3f45defaafb03d528961457a04e3c6f27cfd66"
    (rules "L1.4")
    (case 1 "ti se klama mi" sentence (promised-rows klama)))
  (candidate "samples.md" 16 "33ea8bb4cdb9bbc90f7e759cd40eb0385ce8bef0"
    (rules "L5.9" "L5.8")
    (case 1 "mi na klama" sentence (promised-rows klama)))
  (candidate "samples.md" 17 "14a885a17c62156d54c7ed3a78b6b3908ef59371"
    (rules "L5.12" "L5.8")
    (case 1 "mi klama .ije do stali" sentence (promised-rows klama stali))
    (case 2 "mi klama .ija do stali" sentence (promised-rows klama stali)))
  (candidate "samples.md" 19 "9e3967b0e16d7c22d263f5dd3e873c8babd43e84"
    (rules "L3.1")
    (case 1 "lo mlatu cu blabi" sentence (promised-rows mlatu blabi)))
  (candidate "samples.md" 21 "2876852d13a2e58a91e2a64a38a429d66119040d"
    (rules "L3.1" "L5.9")
    (case 1 "lo mlatu na jbena" sentence (promised-rows mlatu jbena)))
  (candidate "samples.md" 22 "00fe2e7f046eae70ff325b29c40883a520b61c01"
    (rules "L3.2")
    (case 1 "le mlatu cu blabi" sentence (promised-rows mlatu blabi skicu)))
  (candidate "samples.md" 23 "51894d5541b6381e478bca7b33a039b6f96feab4"
    (rules "L3.3")
    (case 1 "la .alis. klama" sentence (promised-rows klama)))
  (candidate "samples.md" 27 "72483335a75e31f291142a3eae2a3a1708356925"
    (rules "L7.4" "L5.22")
    (case 1 "mi joi do" utterance (promised-rows)))
  (candidate "samples.md" 30 "bb927fff8f0424bed33e08d63acaa232f3cca35c"
    (rules "L3.5" "L3.6")
    (case 1 "lo'i gerku" utterance (promised-rows gerku selcmi)))
  (candidate "samples.md" 34 "0381ec3ed5e5eefb48e813e4d611efdafc4c7e78"
    (rules "L3.14" "L3.2" "L3.9" "L3.15")
    (case 1 "lu'o le ci prenu" utterance (promised-rows prenu skicu)))
  (candidate "samples.md" 36 "dcea1ed0a217abde9363445f09a21d766080cca6"
    (rules "L3.4")
    (case 1 "lo'e mlatu cu cinri" sentence (promised-rows mlatu cinri)))
  (candidate "samples.md" 44 "8eac378a0dbb7e9bb101843b6c5f2217febf3ca7"
    (rules "L5.1")
    (case 1 "ro gerku cu blabi" sentence (promised-rows gerku blabi)))
  (candidate "samples.md" 45 "7549d4565ac0ab1e545914425fc678ca69065913"
    (rules "L3.10")
    (case 1 "lo no prenu cu jmaji" sentence (promised-rows prenu jmaji)))
  (candidate "samples.md" 46 "16d5445b9f0efb113e3a9f4a03224a1f770d4959"
    (rules "L5.3")
    (case 1 "ci gerku ce'e re prenu cu nelci" sentence
          (promised-rows gerku prenu nelci)))
  (candidate "samples.md" 48 "7803f54fed3fbabeeb36b7fed9b4b6264bee058c"
    (rules "L5.28")
    (case 1 "so'i prenu cu klama" sentence (promised-rows prenu klama)))
  (candidate "samples.md" 58 "29a4047bce86b1331b60c73b6c86d3a1692b7f97"
    (rules "L1.10")
    (case 1 "mi sutra klama" sentence (promised-rows sutra klama)))
  (candidate "samples.md" 59 "d18b550e979e80e4ef5a9c15530e135e9dc7f869"
    (rules "L5.11")
    (case 1 "ta na'e melbi" sentence (promised-rows melbi)))
  (candidate "samples.md" 63 "f31462b3d6837ee0ae528eb2c40090c63d648886"
    (rules "L5.29")
    (case 1 "ta barda" sentence (promised-rows barda))
    (case 2 "du'e gerku cu klama" sentence (promised-rows gerku klama))
    (case 3 "mi co'e do" sentence (promised-rows)))

  (candidate "spec.md" 1 "e11b80722140960fac027e32c07ce60254e32614"
    (rules "L1.1" "L1.3")
    (case 1 "mi klama ti" predication (promised-rows klama)))
  (candidate "spec.md" 2 "621187d74d9d9df8953e2e731ea712bb08a6e111"
    (rules "L1.4")
    (case 1 "klama fe ti tu" predication (promised-rows klama)))
  (candidate "spec.md" 4 "9d713f6c0194caa64dcf738c85bd1e2918b1b219"
    (rules "L1.4")
    (case 1 "se tavla" selbri (promised-rows tavla)))
  (candidate "spec.md" 9 "4da2df77645deee22f6ddfbb87b1418fa7bfecc5"
    (rules "L5.2")
    (case 1 "ci gerku cu bajra" content (promised-rows gerku bajra)))
  (candidate "spec.md" 10 "30c6bd5c2676ca42a0ec03c53a93c7fdcf91b92d"
    (rules "L5.2" "L0.1")
    (case 1 "ci gerku cu bajra" content (promised-rows gerku bajra)))
  (candidate "spec.md" 19 "a9c634f7bd73b38f2bdda307801f658a9257861d"
    (rules "L5.21")
    (case 1 "mi fa'u do tavla do fa'u mi" content (promised-rows tavla))))
