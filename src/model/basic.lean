import categories.category
import categories.universal.complete

open categories

infixr ` ∙ `:80 := flip category.compose -- type as \.

universe u
variable (C : Type (u+2))
variable [category C]

open categories.universal

instance BinaryCoproducts_from_Cocomplete [Cocomplete C] : has_BinaryCoproducts C := sorry
instance InitialObject_from_Cocomplete [Cocomplete C] : has_InitialObject C := sorry

instance BinaryProducts_from_Complete [Complete C] : has_BinaryProducts C := sorry
instance TerminalObject_from_Complete [Complete C] : has_TerminalObject C := sorry
