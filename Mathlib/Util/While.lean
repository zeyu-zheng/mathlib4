/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/

structure Loop where

variable [Monad m]

@[inline]
partial def Loop.forIn (loop : Loop) (init : β) (f : Unit → β → m (ForInStep β)) : m β :=
  let rec @[specialize] loop (b : β) : m β := do
    match ← f () b with
      | ForInStep.done b  => pure b
      | ForInStep.yield b => loop b
  loop init

instance : ForIn m Loop Unit := ⟨Loop.forIn⟩

macro "repeat " seq:doSeq : doElem =>
  `(doElem| for _ in Loop.mk do $seq)

macro "while " cond:termBeforeDo " do " seq:doSeq : doElem =>
  `(doElem| repeat if $cond then $seq else break)
