(smusni-port-waivers 1
  (waiver
    (case "04cdfd2f45e14a4ad9d525b9aa39518337dfe160")
    (fields effects)
    (finding "#13:issuecomment-5458243084")
    (reason "The A0 equation executes its effectful function at each paired step; the legacy pass-through omits that application effect."))
  (waiver
    (case "5f5b053a4dcccf2858daa126fd3d854e0e78d516")
    (fields effects)
    (finding "#13:issuecomment-5458243084")
    (reason "The A0 equation executes its effectful function at each paired step; the legacy pass-through omits that application effect."))
  (waiver
    (case "27f27c1038df83b40e16a919fdaf24b405d04b04")
    (fields failure-class)
    (finding "#52:issuecomment-5458132092")
    (reason "A0 keeps diagnostics outside its Redex judgment, so this rejected in-bank mutation has no Phase B failure classification yet."))
  (waiver
    (case "4955a8c68f8935068ee2677cd187fc98421260f7")
    (fields failure-class)
    (finding "#52:issuecomment-5458132092")
    (reason "A0 keeps diagnostics outside its Redex judgment, so this rejected in-bank mutation has no Phase B failure classification yet."))
  (waiver
    (case "58c6ffc749c2646868481de082505374ffabf2df")
    (fields failure-class)
    (finding "#52:issuecomment-5458132092")
    (reason "A0 keeps diagnostics outside its Redex judgment, so this rejected in-bank mutation has no Phase B failure classification yet."))
  (waiver
    (case "7482cccbaa630047b71bb8f648818fa1359ddf68")
    (fields failure-class)
    (finding "#52:issuecomment-5458132092")
    (reason "A0 keeps diagnostics outside its Redex judgment, so this rejected in-bank mutation has no Phase B failure classification yet."))
  (waiver
    (case "84d3f3f5db6d9bb097e9df301673052e73e0649a")
    (fields failure-class)
    (finding "#52:issuecomment-5458132092")
    (reason "A0 keeps diagnostics outside its Redex judgment, so this rejected in-bank mutation has no Phase B failure classification yet."))
  (waiver
    (case "8e29fcd7ea73a0b92af918404558667876eff43a")
    (fields failure-class)
    (finding "#52:issuecomment-5458132092")
    (reason "A0 keeps diagnostics outside its Redex judgment, so this rejected in-bank mutation has no Phase B failure classification yet."))
  (waiver
    (case "fb5015ae6fdfa682c9b7f70814a49daf00df1d91")
    (fields failure-class)
    (finding "#52:issuecomment-5458132092")
    (reason "A0 keeps diagnostics outside its Redex judgment, so this rejected in-bank mutation has no Phase B failure classification yet.")))
