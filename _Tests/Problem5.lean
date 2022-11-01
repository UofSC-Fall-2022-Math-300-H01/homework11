import Hw11
import Sets.Basic
import Functions.Basic
import Lean.Elab.Print
import Lean.Elab.Command

open Set
open Func
open Relations 

variable { α : Type }

-- Problem 1 

theorem subset_refl_desired : Reflexive (@Subset α) := sorry 

theorem subset_antisymm_desired : AntiSymmetric (@Subset α) := sorry 

theorem subset_trans_desired : Transitive (@Subset α) := sorry 

-- Problem 2 

def Rel_desired (f : α → α) (a₁ a₂ : α) : Prop := sorry 

theorem refl_id_desired (f : α → α) (h : Reflexive (Rel f) ) : f = id := sorry  

theorem symm_involution_desired (f : α → α) (h : Symmetric (Rel f)) : f ∘ f = id := sorry 

theorem trans_idempotent_desired (f : α → α) (h : Transitive (Rel f)) : f ∘ f = f := sorry 

open Lean
open Lean.Meta
open Lean.Elab.Command

def names : List String := 
  ["subset_refl","subset_antisym","subset_trans","refl_id","symm_involution", "trans_idempotent"]

def n : Nat := 4

def problem : String := names[n]  

def desired : String := problem++"_desired"

def collectAxiomsOf (constName : Name) : MetaM (List String) := do
  let env ← getEnv
  let (_, s) := ((CollectAxioms.collect constName).run env).run {}
  let a := s.axioms.toList.map toString
  return a

#eval isDefEq (Expr.const desired []) (Expr.const problem [])
#eval collectAxiomsOf problem
