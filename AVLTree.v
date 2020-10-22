Inductive Node : Type := 
| null
| node (x:nat) (ls rs :Node).

Inductive cmpType :=
|less
|greater
|equal.

Fixpoint cmp x y : cmpType := 
match x,y with
|0,0 => equal
|S n, 0 => greater
|0, S n => less
|S x, S y => cmp x y
end.

Definition Greater ( x y : nat) : bool :=
  match ( cmp x y ) with
  | greater => true
  | _ => false
  end.

Definition Less ( x y : nat) : bool :=
  match ( cmp x y ) with
  | less => true
  | _ => false
  end.

Notation " x <? y" := (Less x y ) ( at level 50 , left associativity).
Notation " x >? y" := (Greater x y ) ( at level 50 , left associativity).

Fixpoint insert (rt : Node) (val : nat) : Node := 
  match rt with
  | null => node val null null
  | node x ls rs => 
      match cmp val x with
      |equal => rt
      |less  => node x (insert ls val) rs
      |greater => node x ls (insert rs val)
      end
  end.

Notation "x <- y" := (insert x y) (at level 50 , left associativity).

Fixpoint Count (rt : Node) (val : nat ) : bool :=
  match rt with
  |null => false
  |node x ls rs => 
      match cmp val x with
      |equal => true
      |less  => Count ls val
      |greater => Count rs val
     end
 end.

Definition LL_Rotate (rt : Node) : Node :=
 match rt with
|null => null
|node gf (node f fl fr) gfr => node f fl (node gf fr gfr)  
|_ => rt
end.

Definition RR_Rotate (rt : Node) : Node :=
 match rt with
|null => null
|node gf gfl (node f fl fr)  => node f (node gf  gfl fl)  fr
|_ => rt
end.

Definition Max (x y : nat) : nat :=
  match cmp x y with
  |greater => x
  |_ => y
  end.


Fixpoint Depth (rt:Node) : nat := 
  match rt with
  |null => 0
  |node x ls rs => 1 + max (Depth ls) (Depth rs)
end.

Definition t1 := null<-2<-1<-3<-4<-5.

Fixpoint Dif (x y : nat) : nat :=
  match x,y with
  |0,_ => y
  |_,0 => x
  |S x', S y' => Dif x' y'
  end.

Definition LR_Rotate (rt:Node) : Node :=
  match rt with
  | null => null
  | node x ls rs => 
      match ls with
      |null => rt
      |_    => LL_Rotate ( node x (RR_Rotate ls) rs )
     end
end.

Definition RL_Rotate (rt:Node) :Node :=
  match rt with
  | null => null
  | node x ls rs => 
      match rs with
      |null => rt
      |_    => RR_Rotate ( node x ls (LL_Rotate rs) )
     end
end.

Inductive dir : Type :=
|left
|right.

Definition getVal(rt : Node) : nat :=
  match rt with
  | null => 0
  |node x y z => x
  end.


Definition Balance (rt : Node) (val : nat) (d :dir) : Node :=
  match rt with
  |null => null
  |node x ls rs =>
    match (Dif (Depth ls) (Depth rs)) , d with
    |0,_ => rt
    |1,_ => rt
    |_,left => if ( val >? (getVal ls) ) then LL_Rotate rt
               else LR_Rotate rt
    |_,right => if( val <? (getVal rs) ) then RR_Rotate rt
               else RL_Rotate rt
    end
 end.

Fixpoint AVL_insert (rt : Node) (val : nat) : Node := 
  match rt with
  | null => node val null null
  | node x ls rs => 
      match cmp val x with
      |equal => rt
      |less  => Balance ( node x (AVL_insert ls val) rs ) val left  
      |greater => Balance ( node x ls (AVL_insert rs val) ) val right 
      end
  end.

Notation "x <. y" := (AVL_insert x y) ( at level 50 , left associativity).






