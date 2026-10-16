module

public import McsLean.Basic
public import McsLean.ChallengeDefs
public import McsLean.SolutionBridge
public import McsLean.Correctness
public import McsLean.ExecUpdate
public import McsLean.Stability
public import McsLean.Formal_gen001c01_3939115c
public import McsLean.Formal_gen003c01_eea71821
public import McsLean.Exec
public import McsLean.ExecBridge
public import McsLean.BridgeSteps
public import McsLean.CardBridge
public import McsLean.McsInvariant
public import McsLean.BridgePartsA
public import McsLean.BridgePartsB
public import McsLean.BridgePartsC
public import McsLean.BridgeAssembly
public import McsLean.ExecFlip

set_option backward.proofsInPublic true
@[expose] public section
-- All modules above are the Palomar submission artifact. They are imported
-- here so CI (lean-action) builds all of them and the leanchecker step can
-- re-verify every module (the glob in lean_action_ci.yml picks up each
-- built .olean).