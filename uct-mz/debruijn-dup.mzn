% NOTE(vipa, 2023-04-06): The assumed size of a collection
int: n = 100;

enum Repr = {SnocList_Name, ConsList_Name};

% TODO(vipa, 2023-04-06): Problem: the choice thing must
% apply a concrete type. Can I get away with just having,
% e.g., SnocList instead of SnocList_Name or do I need to
% duplicate operations too?
% NOTE(vipa, 2023-04-11): I think this is doable, but it
% requires extra restrictions on the formulation of
% impls/reprs
enum Op_Insert = {SnocList_Snoc, ConsList_Snoc};
function var float: Insert_cost(var Op_Insert: o) =
  if o = SnocList_Snoc then 1 else
  if o = ConsList_Snoc then n else
  0 endif endif; % NOTE(vipa, 2023-04-06): This should be impossible
predicate Insert_choice(var Op_Insert: o, var Repr: r1, var Repr: r2) =
  if o = SnocList_Snoc then r1 = SnocList_Name /\ r2 = SnocList_Name else
  if o = ConsList_Snoc then r1 = ConsList_Name /\ r2 = ConsList_Name else
  true endif endif; % NOTE(vipa, 2023-04-06): This should be impossible

enum Op_Fold = {SnocList_Fold, ConsList_Fold};
function var float: Fold_cost(var Op_Fold: o) =
  if o = SnocList_Fold then n * 1.1 else % NOTE(vipa, 2023-04-06): Extra cost because of fold direction
  if o = ConsList_Fold then n else
  0 endif endif; % NOTE(vipa, 2023-04-06): This should be impossible
predicate Fold_choice(var Op_Fold: o, var Repr: r) =
  if o = SnocList_Fold then r = SnocList_Name else
  if o = ConsList_Fold then r = ConsList_Name else
  true endif endif; % NOTE(vipa, 2023-04-06): This should be impossible

enum Op_FindFirstIdx = {SnocList_FindFirstIdx, ConsList_FindFirstIdx};
function var float: FindFirstIdx_cost(var Op_FindFirstIdx: o) =
  if o = SnocList_FindFirstIdx then n * 1.1 else % NOTE(vipa, 2023-04-06): Extra cost because of FindFirstIdx direction
  if o = ConsList_FindFirstIdx then n else
  0 endif endif; % NOTE(vipa, 2023-04-06): This should be impossible
predicate FindFirstIdx_choice(var Op_FindFirstIdx: o, var Repr: r) =
  if o = SnocList_FindFirstIdx then r = SnocList_Name else
  if o = ConsList_FindFirstIdx then r = ConsList_Name else
  true endif endif; % NOTE(vipa, 2023-04-06): This should be impossible

enum Op_Empty = {SnocList_Empty, ConsList_Empty};
function var float: Empty_cost(var Op_Empty: o) =
  if o = SnocList_Empty then 1 else
  if o = ConsList_Empty then 1 else
  0 endif endif; % NOTE(vipa, 2023-04-06): This should be impossible
predicate Empty_choice(var Op_Empty: o, var Repr: r) =
  if o = SnocList_Empty then r = SnocList_Name else
  if o = ConsList_Empty then r = ConsList_Name else
  true endif endif; % NOTE(vipa, 2023-04-06): This should be impossible

enum Op_Reverse = {SnocList_Reverse, ConsList_Reverse, SnocList_ConsList_Reverse, ConsList_SnocList_Reverse};
function var float: Reverse_cost(var Op_Reverse: o) =
  if o = SnocList_Reverse then n else
  if o = ConsList_Reverse then n else
  if o = SnocList_ConsList_Reverse then 1 else
  if o = ConsList_SnocList_Reverse then 1 else
  0 endif endif endif endif; % NOTE(vipa, 2023-04-06): This should be impossible
predicate Reverse_choice(var Op_Reverse: o, var Repr: r1, var Repr: r2) =
  if o = SnocList_Reverse then r1 = SnocList_Name /\ r2 = SnocList_Name else
  if o = ConsList_Reverse then r1 = ConsList_Name /\ r2 = ConsList_Name else
  if o = ConsList_SnocList_Reverse then r1 = ConsList_Name /\ r2 = SnocList_Name else
  if o = SnocList_ConsList_Reverse then r1 = SnocList_Name /\ r2 = ConsList_Name else
  true endif endif endif endif; % NOTE(vipa, 2023-04-06): This should be impossible

% Somewhat dumb checking of how things scale by just adding
% several independent versions of the same problem
set of int: copy = 1..1;

array[copy] of var Op_Insert: deb_insert;
array[copy] of var Op_FindFirstIdx: deb_findFirstIdx;
array[copy] of var Op_Reverse: deb_reverse;
array[copy] of var Op_Empty: deb_empty;

array[copy] of var Repr: r1;
array[copy] of var Repr: r2;

constraint forall (i in copy) (Empty_choice(deb_empty[i], r1[i]));
constraint forall (i in copy) (Insert_choice(deb_insert[i], r1[i], r1[i]));
constraint forall (i in copy) (Reverse_choice(deb_reverse[i], r1[i], r2[i]));
constraint forall (i in copy) (FindFirstIdx_choice(deb_findFirstIdx[i], r2[i]));

solve minimize sum (i in copy)
  ( Empty_cost(deb_empty[i])
  + Insert_cost(deb_insert[i])
  + Reverse_cost(deb_reverse[i])
  + FindFirstIdx_cost(deb_findFirstIdx[i])
  );
