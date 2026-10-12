import Smusni97.Explicit
open Smusni97.Explicit
-- There is no returned Bool in a Dead arm.
def badDead : Arm false Bool Bool := .live .entry .arg
