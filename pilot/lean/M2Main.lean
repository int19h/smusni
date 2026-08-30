import SmusniPilot.M2Examples

open SmusniPilot

def main : IO Unit := do
  M2.runM2TypingGates
  IO.println <|
    s!"M2 definitions={M2DefinitionId.all.length} " ++
    s!"clauses={M2ClauseId.all.length} typing-rules={M2TypingRuleId.all.length}"
