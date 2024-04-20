import mathlib
import «CatalanNumbers».a_binary_trees

/-- Showing the isomporphism between full binary trees and plane trees. -/

inductive plane_tree : Type
| node : List plane_tree → plane_tree


-- First show that plane tree is isomorphic to List plane tree.

def list_plane_tree_of_plane_tree : plane_tree → List plane_tree
| (plane_tree.node l) => l

def plane_tree_of_list_plane_tree : List plane_tree → plane_tree
| l => plane_tree.node l

theorem list_plane_tree_of_plane_tree_of_list_plane_tree : ∀ (l : List plane_tree), list_plane_tree_of_plane_tree (plane_tree_of_list_plane_tree l) = l := by
  intro l
  induction l
  rfl
  simp [plane_tree_of_list_plane_tree, list_plane_tree_of_plane_tree]
  done

theorem plane_tree_of_list_plane_tree_of_plane_tree : ∀ (t : plane_tree), plane_tree_of_list_plane_tree (list_plane_tree_of_plane_tree t) = t := by
  intro t
  cases t
  simp [plane_tree_of_list_plane_tree, list_plane_tree_of_plane_tree]
  done


-- Second show that List A is isomorphic to 1 + A x List A


-- Third show that plane tree is isomorphc to 1 + plane tree x List plane tree which is ispmorphic to 1 + plane tree


-- Then use bijection X -> 1 + X^2 to show that bin tree is isomorphic to 1 + bin tree^2-/


-- Alternatively: some sort of direct inductive transformation
def full_binary_tree_of_plane_tree : plane_tree → full_binary_tree
| .node [] => full_binary_tree.node .leaf .leaf
-- | .node [T] => full_binary_tree.node (full_binary_tree_of_plane_tree T) .leaf
| .node (T :: l) => full_binary_tree.node (full_binary_tree_of_plane_tree T) (full_binary_tree_of_plane_tree (plane_tree.node l))

def plane_tree_of_full_binary_tree : full_binary_tree → plane_tree
| full_binary_tree.leaf => plane_tree.node []
| full_binary_tree.node T₁ T₂ => plane_tree.node [plane_tree_of_full_binary_tree T₁, plane_tree_of_full_binary_tree T₂]

theorem full_binary_tree_of_plane_tree_of_full_binary_tree : ∀ (t : full_binary_tree), full_binary_tree_of_plane_tree (plane_tree_of_full_binary_tree t) = t := by
  sorry

theorem plane_tree_of_full_binary_tree_of_plane_tree : ∀ (t : plane_tree), plane_tree_of_full_binary_tree (full_binary_tree_of_plane_tree t) = t := by
  sorry
