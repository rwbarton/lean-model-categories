import categories.category
import categories.universal.complete

import model.basic
import model.morphism_class
import model.weq
import model.wfs

open categories
open categories.universal

-- Fix a category C.
universe u
variable (C : Type (u+2))
variable [category C]


namespace model

class ModelCategory [Complete C] [Cocomplete C] :=
  (weq cof fib : MorphismClass C)
  (weq_ok : IsWeakEquivalences weq)
  (caf : IsWFS cof (weq ∩ fib)) 
  (acf : IsWFS (weq ∩ cof) fib) 

-- XXX below is ugly
variable {C}
variables [category C] [Complete C] [Cocomplete C] [ModelCategory C]
def weq := ModelCategory.weq C
def cof := ModelCategory.cof C
def fib := ModelCategory.fib C
def acof := ModelCategory.weq C ∩ ModelCategory.cof C
def afib := ModelCategory.weq C ∩ ModelCategory.fib C

def caf := ModelCategory.caf C
def acf := ModelCategory.acf C

/-
def cof_of_acof {X Y : C} (f : X ⟶ Y) : acof f → cof f := λ a, a.left
def weq_of_acof {X Y : C} (f : X ⟶ Y) : acof f → weq f := λ a, a.right

def fib_of_afib {X Y : C} (f : X ⟶ Y) : afib f → fib f := λ a, a.left
def weq_of_afib {X Y : C} (f : X ⟶ Y) : afib f → weq f := λ a, a.right
-/

-- XXX HELP NOTATION
def cofibrant (A : C) : Prop :=
  cof ((has_InitialObject.initial_object C).morphism_from_initial_object_to A)
def fibrant (X : C) : Prop :=
  fib ((has_TerminalObject.terminal_object C).morphism_to_terminal_object_from X)

end model
