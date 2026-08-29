import SmusniPilot

open SmusniPilot

def main (arguments : List String) : IO UInt32 := do
  let root := arguments.head?.getD "../.."
  runLocalGates
  let generated ← runGeneratedRoundTrips
  let result ← runS1 root
  IO.println <|
    s!"S1 total={result.total} primitive={result.primitive} " ++
      s!"pending-m2={result.pendingM2} out-of-slice={result.outOfSlice} " ++
      s!"core-decoded={result.decodedCore} " ++
      s!"surface-roundtrips={result.surfaceRoundTrips} " ++
      s!"text-roundtrips={result.textRoundTrips} " ++
      s!"generated-roundtrips={generated}"
  return 0
