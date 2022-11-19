/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

import Mathlib.Mathport.Rename
import Std.Data.RBMap.Basic

/-!
# Red Black Trees

Deprecated definitions -- use `Std.RBSet` instead.

TODO: Delete post porting
-/

universe u v

section
set_option linter.deprecated false
-- FIXME: remove this when the sorries are gone
set_option warningAsError false


/-- Nodes of an Red Black Tree-/
@[deprecated Std.RBNode] inductive RBNode (α : Type u) where
  /-- leaf (empty marker) node-/
  | leaf : RBNode α
  /-- red node-/
  | red_node (lchild : RBNode α) (val : α) (rchild : RBNode α ) : RBNode α
  /-- black node-/
  | black_node (lchild : RBNode α) (val : α) (rchild : RBNode α) : RBNode α

#align rbnode Std.RBNode

def MemExact : α → RBNode α → Prop := sorry
def Mem : α → RBNode α → Prop := sorry
def depth (f : Nat → Nat → Nat) : RBNode α → Nat := sorry


/-- Note changed from `def` to `structure` to simplify the
    previous autoparameter tactic issues -/
@[deprecated Std.RBMap] structure RBTree (α : Type u) where
  mk :: (h: RBNode α) (cmp: α → α → Prop)

#align rbtree Std.RBMap

namespace RBTree


end RBTree
end
