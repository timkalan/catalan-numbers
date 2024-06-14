import «CatalanNumbers».definitions
import «CatalanNumbers».list_plane_tree_isomorphism -- imported task 4

-- 5. Rotating isomorphism between full binary trees and plane trees
-- Define both directions as functions and prove that they are inverses of each other

-- Definition of transformation from plane tree to full binary tree
def full_binary_tree_of_plane_tree : plane_tree → full_binary_tree
| plane_tree.node [] => full_binary_tree.leaf
| plane_tree.node (T :: l) => full_binary_tree.node (full_binary_tree_of_plane_tree T) (full_binary_tree_of_plane_tree (plane_tree.node l))


-- Definition of transformation from full binary tree to plane tree
def plane_tree_of_full_binary_tree : full_binary_tree → plane_tree
| full_binary_tree.leaf => plane_tree.node []
| full_binary_tree.node T₁ T₂ => plane_tree.node (plane_tree_of_full_binary_tree T₁ :: list_plane_tree_of_plane_tree (plane_tree_of_full_binary_tree T₂))

-- Proof that the transformations are inverses of each other
theorem full_binary_tree_of_plane_tree_of_full_binary_tree : ∀ (t : full_binary_tree), full_binary_tree_of_plane_tree (plane_tree_of_full_binary_tree t) = t := by
  intro t
  induction t with
  | leaf => rfl
  | node T₁ T₂ ih₁ ih₂ =>
    simp [full_binary_tree_of_plane_tree, plane_tree_of_full_binary_tree]
    rw [ih₁]
    simp  -- Remove T₁ = T₁ from the goal
    rw [plane_tree_of_list_plane_tree_of_plane_tree] -- use of the isomorphism list plane tree ≅ plane tree
    rw [ih₂]
    done

theorem plane_tree_of_full_binary_tree_of_plane_tree : ∀ (t : plane_tree), plane_tree_of_full_binary_tree (full_binary_tree_of_plane_tree t) = t := by
  rintro ⟨⟨ ⟩ | ⟨T₁, l⟩⟩ -- here we have to use rintro because induction does not work
  -- case where t = plane_tree.node []
  rfl
  -- case where t = plane_tree.node (T₁ :: l)
  simp [full_binary_tree_of_plane_tree, plane_tree_of_full_binary_tree]
  rw [plane_tree_of_full_binary_tree_of_plane_tree] -- to use the induction hypothesis we call the theorem we are proving
  rw [plane_tree_of_full_binary_tree_of_plane_tree]
  simp
  rw [list_plane_tree_of_plane_tree_of_list_plane_tree] -- use of the isomorphism list plane tree ≅ plane tree
  done
