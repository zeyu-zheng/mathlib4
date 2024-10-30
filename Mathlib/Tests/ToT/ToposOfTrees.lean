import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Functor.Const
import Mathlib.CategoryTheory.ChosenFiniteProducts
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.Tests.ToT.ToT
import Mathlib.Tests.ToT.Lemmas
import Mathlib.Tests.ToT.Categories

open CategoryTheory

namespace Guardedlean


/--- Topos of Trees---/
abbrev ToposOfTrees := ℕᵒᵖ ⥤ Type

-- Equality in the Topos of Tree only has to be checked on arrow of size 1
lemma ToposOfTrees.extentionality (X Y : ToposOfTrees) (eObj : ∀ n, X.obj n = Y.obj n)
    (eMap : ∀ n (e : Opposite.op (n+1) ⟶ Opposite.op n),
     X.map e = (eObj (Opposite.op n)) ▸ (eObj (Opposite.op (n+1))) ▸ (Y.map e)) : X = Y := by {
    match X,Y with | {obj := Xobj, map := Xmap,map_id := Xid,map_comp := Xcomp},
                     {obj := Yobj, map := Ymap,map_id := Yid,map_comp := Ycomp} => {
      have e := funext eObj
      simp at e
      cases e
      congr
      simp at eMap Xcomp Ycomp Xid Yid
      funext (Opposite.op n) (Opposite.op m) (Opposite.op f) x
      simp at f
      apply ℕ.catInduction (λ a b g => ∀ x, Xmap (Opposite.op g) x = Ymap (Opposite.op g) x)
      clear n m f x
      intros n x
      have eid : Opposite.op (𝟙 n) = 𝟙 (Opposite.op n) := by rfl
      rw [eid, Xid, Yid]
      simp
      clear n m f x
      intros n f x
      rw [eMap]
      clear n m f x
      intros n k m f g e₁ e₂ x
      have efg : Opposite.op (f ≫ g) = (@CategoryStruct.comp _ _ (Opposite.op m) (Opposite.op k) (Opposite.op n) (Opposite.op g) (Opposite.op f)) := by rfl
      rw [efg]
      rw [Xcomp,Ycomp]
      simp
      rw [e₁,e₂]
    }
  }


/--- Equivalence between ToT and ToposOfTrees ---/

private def G : ToposOfTrees ⥤ ToT where
  obj X := {
    set := λ n => X.obj (Opposite.op n),
    restrict := λ n => X.map (makeOpArrow (Nat.le_add_right n 1))
  }
  map {X Y} f := {
    setMorph := λ n x => f.app (Opposite.op n) x
    restrictMorph := λ n => by {
      simp
      rw [Function.comp_def, Function.comp_def,<-Function.comp_def,<-Function.comp_def]
      symm
      apply (f.naturality (makeOpArrow (Nat.le_add_right n 1)))
    }
  }

set_option maxHeartbeats 3200000
set_option aesop.dev.statefulForward true in
--set_option trace.profiler true in
private def F : ToT ⥤ ToposOfTrees := {
  obj := λ o => {
    map := λ {n m} f x =>
      have eq : m.unop + (n.unop - m.unop) = n.unop := by
        rw [Nat.add_sub_cancel']
        exact f.unop.down.down
      
      ToT.iterRestrict o m.unop (n.unop - m.unop) n.unop (by omega) x
    map_id := by
      intro o
      funext xw
      simp only [id_eq, eq_mpr_eq_cast, Int.reduceNeg, Nat.sub_self, types_id_apply]
      unfold ToT.iterRestrict
      rfl
    map_comp := by
      intro m n p f g
      funext x
      simp only [id_eq, eq_mpr_eq_cast, Int.reduceNeg, types_comp_apply]
      symm
      simp only at x
      rw [ToT.iterRestrictComp o (Opposite.unop n) (Opposite.unop m) (Opposite.unop p) _ _ _ _ x]
      congr
      apply unmakeOpArrow at f
      apply unmakeOpArrow at g
      omega
  },
  map := λ {X Y} η => {
    app := λ n x => η.setMorph n.unop x
    naturality := λ {m n} p => by {
      simp only [id_eq, eq_mpr_eq_cast, Int.reduceNeg, unop_id, types_id_apply, Nat.add_zero,
        cast_eq, unop_comp, types_comp_apply]
      funext x
      simp only [types_comp_apply]
      rw [compDefExt (η.setMorph (Opposite.unop n))]
      rw [<-ToTMorphism.restrictMorphLift]
      simp only [Function.comp_apply]
    }
  }
}

lemma Guardedlean.ToposOfTrees.extentionality' (X Y : ToposOfTrees)
    (eObj : ∀ (n : ℕᵒᵖ), X.obj n = Y.obj n)
   : X = Y := by sorry

set_option aesop.dev.statefulForward true in
set_option trace.profiler true in
example (X : ToposOfTrees)
(n m : ℕᵒᵖ)
(f : n ⟶ m)
(x : (Guardedlean.F.obj (Guardedlean.G.obj X)).obj n)
(h : ∀ (n : ℕᵒᵖ), (Guardedlean.F.obj (Guardedlean.G.obj X)).obj n = X.obj n)
: True := by 
  saturate [Guardedlean.ToposOfTrees.extentionality', *]
  --have : ∀ (n : ℕ) (f : Opposite.op (n + 1) ⟶ Opposite.op n), (Guardedlean.F.obj (Guardedlean.G.obj X)).map f = ⋯ ▸ ⋯ ▸ X.map f := sorry
  obtain t1 :=
    ToposOfTrees.extentionality (F.obj (G.obj X))
      X (_) (_)
  trivial
  

def TTooTTequivalence : ToT ≌ ToposOfTrees := {
  functor := F
  inverse := G
  unitIso := {
    hom := {
      app := λ X => {
        setMorph := λ n x => x
        restrictMorph := λ n => by {
          simp
          rw [<-Function.id_def,<-Function.id_def,Function.comp_id,Function.id_comp]
          funext x
          unfold F G
          simp
          unfold ToT.iterRestrict
          rfl
        }
      }
    }
    inv := {
      app := λ X => {
        setMorph := λ n x => x
        restrictMorph := λ n => by {
          funext x
          simp
          unfold F G
          simp
          unfold ToT.iterRestrict
          simp
          rw [ToT.iterRestrictZero]
        }
      }
    }
  }
  counitIso := {
    hom := {
      app := λ X => {
        app := λ n x => x
        naturality := λ n m f => by {
          simp
          funext x
          simp
          have ext := ToposOfTrees.extentionality (F.obj (G.obj X)) X (λn=>by rfl) (λn f => by funext x;unfold F G;simp;unfold ToT.iterRestrict;simp;rw [ToT.iterRestrictZero];congr)
          have applied := @Eq.rec _ (F.obj (G.obj X)) (fun Y (e : F.obj (G.obj X) = Y) => (F.obj (G.obj X)).map f x = cast (congrArg (fun ξ => ξ.obj m) (Eq.symm e)) (Y.map f (cast (congrArg (fun ξ => ξ.obj n) e) x))) (by rfl) _ ext
          rw [applied]
          simp
        }
      }
    }
    --TODO merge with object and proof above ?
    inv := {
      app := λ X => {
        app := λ n x => x
        naturality := λ n m f => by {
          simp
          funext x
          simp
          have ext := ToposOfTrees.extentionality (F.obj (G.obj X))
            X (λn=>by rfl) (λn f => by funext x;unfold F G;simp;unfold ToT.iterRestrict;simp;rw [ToT.iterRestrictZero];congr)
          have applied := @Eq.rec _ (F.obj (G.obj X))
            (fun Y (e : F.obj (G.obj X) = Y) => (F.obj (G.obj X)).map f x = cast (congrArg (fun ξ => ξ.obj m) (Eq.symm e)) (Y.map f (cast (congrArg (fun ξ => ξ.obj n) e) x))) (by rfl) _ ext
          rw [applied]
          simp
        }
      }
    }
  }
  functor_unitIso_comp := by {
    intro X
    simp
    congr
  }
}