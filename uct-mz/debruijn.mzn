% NOTE(vipa, 2023-04-06): The assumed size of a collection
int: n = 100;

enum Repr = {SnocList_Name, ConsList_Name};

% TODO(vipa, 2023-04-06): Problem: the choice thing must
% apply a concrete type. Can I get away with just having,
% e.g., SnocList instead of SnocList_Name or do I need to
% duplicate operations too?
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


var Op_Insert: deb_insert;
var Op_FindFirstIdx: deb_findFirstIdx;
var Op_Reverse: deb_reverse;
var Op_Empty: deb_empty;

var Repr: r1;
var Repr: r2;

constraint Empty_choice(deb_empty, r1);
constraint Insert_choice(deb_insert, r1, r1);
constraint Reverse_choice(deb_reverse, r1, r2);
constraint FindFirstIdx_choice(deb_findFirstIdx, r2);

solve minimize
  Empty_cost(deb_empty)
  + Insert_cost(deb_insert)
  + Reverse_cost(deb_reverse)
  + FindFirstIdx_cost(deb_findFirstIdx);
