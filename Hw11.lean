import Sets.Basic
import Functions.Basic
import Relations.Basic

open Set
open Func
open Relations 

variable { α : Type }

-- Problem 1 

theorem subset_refl : Reflexive (@Subset α) := fun _ => sub_refl 

theorem subset_antisymm : AntiSymmetric (@Subset α) := by 
  intro X Y h₁ h₂
  exact set_ext.mpr (fun x => ⟨h₁ x, h₂ x⟩) 

theorem subset_trans : Transitive (@Subset α) := fun _ _ _ h₁ h₂ x h => h₂ x (h₁ x h)

-- Problem 2 

def Rel (f : α → α) (a₁ a₂ : α) : Prop := f a₁ = a₂ 

theorem refl_id (f : α → α) (h : Reflexive (Rel f) ) : f = id := by 
  apply funext 
  intro a 
  exact h a 

theorem symm_involution (f : α → α) (h : Symmetric (Rel f)) : f ∘ f = id := by 
  apply funext 
  intro x 
  have : Rel f x (f x) := by rfl 
  have : Rel f (f x) x := h this 
  exact this 

theorem trans_idempotent (f : α → α) (h : Transitive (Rel f)) : f ∘ f = f := by 
  apply funext 
  intro x 
  have h₁ : Rel f x (f x) := by rfl 
  have h₂ : Rel f (f x) (f (f x)) := by rfl 
  have h₃ : Rel f x (f (f x)) := h h₁ h₂ 
  exact Eq.symm h₃ 

