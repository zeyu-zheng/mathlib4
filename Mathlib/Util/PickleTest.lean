import Mathlib.Util.Pickle

open Lean Elab Command

elab "#pickle" : command => liftTermElabM do
  pickle "pickle.olean" (List.range 10000000)

#pickle
