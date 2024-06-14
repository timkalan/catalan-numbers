import «CatalanNumbers».definitions

-- 4. list plane tree ≅ plane tree
-- Define both directions as functions and prove that they are inverses of each other
-- One direction is simply plane_tree.node, the other is given by:
def list_plane_tree_of_plane_tree : plane_tree → List plane_tree
| (plane_tree.node l) => l

-- Proof that the transformations are inverses of each other
theorem list_plane_tree_of_plane_tree_of_list_plane_tree : ∀ (l : List plane_tree), list_plane_tree_of_plane_tree (plane_tree.node l) = l := by
  intro l
  cases l with
  | nil => rfl
  | cons hd tl =>
    simp [plane_tree.node, list_plane_tree_of_plane_tree]
    done
  -- or simply:
  -- exact fun l ↦ rfl

theorem plane_tree_of_list_plane_tree_of_plane_tree : ∀ (t : plane_tree), plane_tree.node (list_plane_tree_of_plane_tree t) = t := by
  intro t
  cases t with
  | node l => simp [plane_tree.node, list_plane_tree_of_plane_tree]
  done
