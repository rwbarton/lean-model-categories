import categories.functor
import categories.graphs
import categories.path_category
import categories.universal.complete

open categories
open categories.functor
open categories.graphs
open categories.universal

namespace categories.pushout

-- TODO:
-- * Define structures of cospans, squares.
-- * Show that the pushout of a cospan is a square with a universal property.
--   I guess before that, we can define the universal property "is_pushout"
--   and prove the pasting lemma for it

universe u
/- The indexing category for pushouts is the free category on a graph. -/
-- Objects
inductive PO : Type (u+1)
| a
| b
| c

-- Edges, i.e., generating morphisms
inductive GrPO : PO → PO → Type u
| ab : GrPO PO.a PO.b
| ac : GrPO PO.a PO.c
instance : graph PO := ⟨GrPO⟩

-- The indexing category itself
def PO_J := Path PO
instance : category PO_J := categories.graphs.PathCategory PO

/- Construction of diagrams indexed on PO_J -/
section hom_def
-- XXX This seems like a gratuitous number of universes.
parameter {M : Type (u+3)}
parameter [category M]

parameters {A B C : M}
parameters (f : A ⟶ B) (g : A ⟶ C)

def vert_hom : PO → M
| PO.a := A
| PO.b := B
| PO.c := C

def edge_hom : Π (v : PO) (w : PO), GrPO v w → Hom (vert_hom v) (vert_hom w)
| _ _ GrPO.ab := f
| _ _ GrPO.ac := g
end hom_def

variable {M : Type (u+3)}
variable [category M]

protected def gr_hom {A B C : M} (f : A ⟶ B) (g : A ⟶ C) :
  graph_homomorphism PO M :=
  { onVertices := vert_hom,
    onEdges := edge_hom f g }

def cospan_functor {A B C : M} (f : A ⟶ B) (g : A ⟶ C) : Functor PO_J M :=
  Functor.from_GraphHomomorphism (categories.pushout.gr_hom f g)

def pushout_cocone [Cocomplete M] {A B C : M} (f : A ⟶ B) (g : A ⟶ C) :
  ColimitCocone (cospan_functor f g)
  := colimitCocone (cospan_functor f g)

def pushout [Cocomplete M] {A B C : M} (f : A ⟶ B) (g : A ⟶ C) : M
  := (pushout_cocone f g).initial_object.cocone_point

end categories.pushout
