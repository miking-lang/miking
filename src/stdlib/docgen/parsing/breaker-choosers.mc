-- # BreakerChooser system: choosing breakers and managing parse state
--
-- This module defines a set of `BreakerChoosers`, one per parsing state.
--
-- It defines the automaton of our parser. The idea is that, depending on the current state,
-- when reading an opener, we don’t want to select the same breakers or transition into the same states.
--
-- For example, if we are in the `Lang {}` state, we want `end` to be considered a `type` breaker.
-- Whereas if we are in the `Program` state, it is unnecessary to treat `end` as a type breaker—even
-- though doing so would not affect the parser’s validity.
--
-- The core concept is that parsing is guided by a state machine:
-- - The current **state** determines what the parent node is.
-- - A **breaker** is a token that closes one or more blocks.
-- - When a token is encountered, the BreakerChooser can decide:
--     * What are the breakers of this new block? (`choose`)
--     * Should parsing continue under the same parent node? (`continue`)
--       For example, if we have `lang sem A = sem B = end`, the second `sem` will break the first `sem`,
--       but we want to continue parsing under the `lang` parent. On the other hand, when we see `end`,
--       it breaks the second `sem`, and we do not want to continue parsing under the `lang` parent.
--     * Should this breaker be absorbed? (`absorbIt`)
--       In the previous example, the second `sem` does not absorb its breaker (it belongs to the parent block),
--       whereas the `Lang {}` block does absorb the `end`. The automaton decides whether a block in a given state
--       is allowed to absorb its breaker.
--     * Is this a hard break? (`reStructureTree`)
--       The automaton determines whether a given break is hard. For example, if a `let` is broken by `lang`,
--       we must restructure the tree and reinterpret that `let` as a `TopLet`.
--     * What is the alternate version of this state? (`switchVersion`)
--       When switching states (e.g., from `Let` to `TopLet`), this determines what the new state should be.
--
-- The entire system is composed at the bottom into a single `BreakerChooser`.


include "./lexing/token-readers.mc"


-- Interface for a BreakerChooser; all choosers implement this contract.
-- Each function has a default implementation so that not all sems need to be defined explicitly.
lang BreakerChooserInterface = TokenReader

    -- A breaker is a set of Strings representing all possible breakers
    -- for a block, along with the state of this block.
    type Breaker = { breakers: [String], state: State }

    -- Parser automaton states.
    syn State = 
        | StateProgram {}
        | StateTopLet {}
        | StateRecLet {}        
        | StateLet {}
        | StateTopRec {}
        | StateRec {}
        | StateLang {}
        | StateTopType {}
        | StateType {}
        | StateTopUse {}
        | StateUse {}
        | StateSem {}
        | StateSyn {}
        | StateCon {}
        | StateTopCon {}
        | StateMexpr {}
        | StateUtest {}
        | StateTopUtest {}

    -- Human-readable name for a State.
    sem toString: State -> String
    sem toString =
        | StateProgram {} -> "Program"
        | StateTopLet {} -> "TopLet"
        | StateRecLet {} -> "RecLet"        
        | StateLet {} -> "Let"
        | StateLang {} -> "Lang"
        | StateTopRec {} -> "TopRec"
        | StateRec {} -> "Rec"
        | StateTopType {} -> "TopType"
        | StateType {} -> "Type"
        | StateSem {} -> "Sem"
        | StateSyn {} -> "Syn"
        | StateCon {} -> "Con"
        | StateTopCon {} -> "TopCon"
        | StateMexpr {} -> "Mexpr"
        | StateUse {} -> "Use"
        | StateUtest {} -> "Utest"
        | StateTopUtest {} -> "TopUtest"


    -- Determine the new state and the breakers after encountering a block opener.
    -- The default behavior is to crash since this would mean the automaton is wrong.
    -- For a valid automaton, all cases must be handled.
    sem choose : (State, String, Pos) -> Breaker
    sem choose =
      | (state, word, pos) -> error (join ["Parsing Failed, x: ", int2string pos.x, ", y: ", int2string pos.y, ": ", "You cannot have the word ", word, " inside a ", (toString state), " block."])

    -- Determine if, for a given breaker, tokenization should continue for the parent state.
    -- The default behavior is to continue.
    sem continue : (State, String) -> Bool
    sem continue =
        | (state, word) -> true

    -- Determine if the block becomes hard in a given context.
    -- The default behavior is to not restructure the tree.
    sem reStructureTree: (State, String) -> Bool
    sem reStructureTree =
        | (_, _) -> false

    -- Determine whether the breaker should be part of the current block or part of the parent block.
    -- The default behavior is to reject the breaker.
    sem absorbIt : (State, String) -> Bool
    sem absorbIt  =
        | (state, word) -> false

    -- Takes a state and its breaker and returns the correct version of the state if it must change.
    -- The default behavior is to keep the same state.
    sem switchVersion : (State, String) -> State
    sem switchVersion =
        | (state, _) -> state
        
    -- Helper to build a Breaker from a breaker list and a state.
    sem build : [String] -> State -> Breaker
    sem build =
    | breakers -> lam state. { breakers = breakers, state = state }

     
end

-- Defining some constants for breaker states

-- This block can only close on "in".
let innerBloc = ["in"]

-- Breakers for recursive objects: these are the literal representations of recursive enders.
let recBreak = ["#in", "#end"]

-- Breakers for a recursive block that can only end with "in".
let recInner = ["#in"]

-- Breakers for a top-level recursive block.
let recOuter = ["#end"]

-- Breakers for top-level objects.
-- We cannot consider let, type, etc. as explicit breakers
-- since they could be nested.
let topLvlBreak = ["lang", "mexpr"]

-- Breakers for top-level blocks that do not contain any nested blocks,
-- so they can be instantly broken by any opener since nesting is impossible.
let topLvlAnyBreak = concat topLvlBreak ["let", "recursive", "con", "type", "mexpr", "utest"]

-- Same as topLvlBreak, but when the block could be nested and thus may also end with "in".
let innerCandidateBreak = concat ["in", "#in"] topLvlBreak

-- Same as topLvlAnyBreak, but when the block could be nested and thus may also end with "in".
let innerCandidateAnyBreak = cons "in" topLvlAnyBreak

-- All top-level lang keywords that can only break. Syntactically,
-- it is impossible for these blocks to be nested.
-- For example, we cannot have a sem inside a sem.
let langBreak = ["end", "sem", "syn"]

-- Here we also consider type and con, which are top-level lang keywords,
-- but they are special since they can be nested.
let langFullBreak = concat ["type", "con"] langBreak

-- Finally, here we also consider "in".
-- We use this when the block could be nested.
let langFullBreakIn = cons "in" langFullBreak 

-- At the root of the program, we can find any top-level block,
-- and we can assume with certainty that each block is top-level.
lang ProgramBreakerChooser = BreakerChooserInterface

     -- The choose implementation has 4 main cases:
     -- 1. type and con are very simple blocks without nested blocks, so anything breaks them without ambiguity.
     -- 2. lang and recursive are also simple since they are closed with only one keyword. Note that #end is the literal form of RecursiveEnder.
     -- 3. let and utest are more restricted: we cannot treat let as a breaker since it may be nested. Therefore,
     --    the only breakers are words that can only exist at the top level.
     -- 4. mexpr is the easiest case, as it cannot break—it is always the last top-level block.
    sem choose =        
        | (StateProgram {}, "type", pos) -> build topLvlAnyBreak (StateTopType {})
        | (StateProgram {}, "con", pos) -> build topLvlAnyBreak (StateTopCon {})

        | (StateProgram {}, "lang", pos) -> build ["end"] (StateLang {})
        | (StateProgram {}, "recursive", pos) -> build recOuter (StateTopRec {})

        | (StateProgram {}, "let", pos) -> build topLvlBreak (StateTopLet {})
        | (StateProgram {}, "utest", pos) -> build topLvlBreak (StateTopUtest {})

        | (StateProgram {}, "mexpr", pos) -> build [] (StateMexpr {})

    -- At the top level, every breaker is absorbed.
    sem absorbIt =
        | (StateProgram {}, word) -> true

end

-- Handles the mexpr case. This is simple since all its components
-- are guaranteed to be inner blocks and nothing can break it.
lang MexprBreakerChooser = BreakerChooserInterface

    -- All blocks are inner blocks, so we assume they close with "in".
    -- Only recursive is closed with #in, the literal form of RecursiveEnder.
    sem choose =
    | (StateMexpr {}, "let", pos) -> build innerBloc (StateLet {})
    | (StateMexpr {}, "utest", pos) -> build innerBloc (StateUtest {})
    | (StateMexpr {}, "type", pos) -> build ["in"] (StateType {})
    | (StateMexpr {}, "con", pos) -> build ["in"] (StateCon {})
    | (StateMexpr {}, "use", pos) -> build ["in"] (StateUse {})

    | (StateMexpr {}, "recursive", pos) -> build recInner (StateRec {})
    
end


-- In this language we handle both top-level and inner let/utest blocks.
-- The main idea is that when a TopLet encounters a `let`, it cannot know beforehand
-- whether it is an inner let or not. So it assumes it is, and gives it the possibility
-- to break on "in". If later the `let` breaks on a top-level keyword such as `lang` or `mexpr`,
-- this triggers a reconstruction.
-- In other words, any `Let` can potentially be a `TopLet`, so we must apply the same rules
-- when encountering "let" inside a Let. Utests behave in exactly the same way.
lang LetUtestBreakerChooser = BreakerChooserInterface

    -- Similar to Program blocks, we have 4 cases:
    -- 1. let and utest are ambiguous, but they can now also break on "in".
    -- 2. For type and con, the same logic applies, but they can also break on "in".
    -- 3. Recursive can now break on both "#end" and "#in", since we cannot know beforehand if it is top-level.
    -- 4. use always ends with "in".
    sem choose =
        | (StateLet {} | StateUtest {} | StateTopLet {} | StateTopUtest {}, "let", pos) -> build innerCandidateBreak (StateLet {})
        | (StateLet {} | StateUtest {} | StateTopLet {} | StateTopUtest {}, "utest", pos) -> build innerCandidateBreak (StateUtest {})

        | (StateLet {} | StateUtest {} | StateTopLet {} | StateTopUtest {}, "type", pos) -> build innerCandidateAnyBreak (StateType {})
        | (StateLet {} | StateUtest {} | StateTopLet {} | StateTopUtest {}, "con", pos) -> build innerCandidateAnyBreak (StateCon {})
        
        | (StateLet {} | StateUtest {} | StateTopLet {} | StateTopUtest {}, "recursive", pos) -> build recBreak (StateRec {})
        
        | (StateLet {} | StateUtest {} | StateTopLet {} | StateTopUtest {}, "use", pos) -> build innerBloc (StateUse {})

    -- For an inner block, we only continue parsing the parent
    -- if the breaker is "in".
    -- For top-level blocks, we always continue, since their parent is always Program.
    sem continue =
        | (StateLet {} | StateUtest {}, !"in") -> false

    -- If we close an inner block with anything other than "in",
    -- it means it was not inner, so we trigger a restructuring.
    sem reStructureTree =
        | (StateLet {} | StateUtest {}, !"in") -> true

    -- Let/utest will only absorb "in"; other breakers usually
    -- start new blocks such as lang.
    sem absorbIt =
        | (StateLet {} | StateUtest {}, "in") -> true

    -- If the block does not end with "in", we cast inner let/utest
    -- to their top-level versions. 
    -- The special case is if we break on a recursive ender like "#in":
    -- this means the let was actually a RecLet.
    sem switchVersion =
        | (StateUtest {}, !"in") -> StateTopUtest {}
        | (StateLet {}, "#in" | "#end") -> StateRecLet {}        
        | (StateLet {}, !"in") -> StateTopLet {}

end

-- Here we handle the LetRec case, which is quite similar to the TopBreakerChooser,
-- but simpler since only let blocks are ambiguous.
lang LetRecBreakerChooser = BreakerChooserInterface

    -- We have 3 cases:
    -- 1. let is still ambiguous—we cannot know if it is a RecLet or a nested Let.
    --    So we include both "in" and RecursiveEnder (#in/#end) and assume nested,
    --    then fix later if it is not.
    -- 2. utest, type, con, and use are straightforward: inside a recursive,
    --    they can only be inner blocks.
    -- 3. recursive can also only be an inner block, so it has a single breaker.
    sem choose =
        | (StateRecLet {}, "let", pos) -> build ["in", "#end", "#in"] (StateLet {})
        
        | (StateRecLet {}, "utest", pos) -> build innerBloc (StateUtest {})
        | (StateRecLet {}, "type", pos) -> build innerBloc (StateType {})
        | (StateRecLet {}, "con", pos) -> build innerBloc (StateCon {})
        | (StateRecLet {}, "use", pos) -> build innerBloc (StateUse {})
        
        | (StateRecLet {}, "recursive", pos) -> build recInner (StateRec {})

    -- We never continue a RecLet that has broken,
    -- since its breakers (#end and #in) also break the recursive parent block.
    sem continue =
        | (StateRecLet {}, _) -> false
end

-- This is the language for Rec blocks, including both TopRec and ambiguous inner Rec.
lang RecBreakerChooser = BreakerChooserInterface

    -- Recursive blocks can only open on let, so we know it is a RecLet.
    -- A TopRec does not need to include "#in" in its breakers,
    -- since we know it ends with "#end".
    sem choose =
        | (StateTopRec {}, "let", pos) -> build recOuter (StateRecLet {})
        | (StateRec {}, "let", pos) -> build recBreak (StateRecLet {})
        
    -- Rec blocks end with #end or #in, which are part of the block, so they are absorbed.
    sem absorbIt =
        | (StateRec {} | StateTopRec {}, _) -> true

    -- If a Rec block ends with #end, it was actually a TopRec,
    -- so we must trigger a reconstruction.
    sem reStructureTree =
        | (StateRec {}, "#end") -> true

    -- If we encounter #end, it means our current parent is not the real parent.
    -- We must stop execution and restructure the tree correctly.
    sem continue =
        | (StateRec {}, "#end") -> false

    -- If the Rec ends with #end, cast it into TopRec.
    sem switchVersion =
        | (StateRec {}, "#end") -> StateTopRec {}
end
    
-- This language handles both con and type, which behave identically.
-- A top-level con/type is easy to handle, as it can only contain use blocks,
-- which only break on "in".
-- The inner version is slightly harder—not because it can contain sub-blocks (it cannot),
-- but because we must handle possible restructuring.
lang TypeConBreakerChooser = BreakerChooserInterface

    sem choose =
        | (StateType {} | StateCon {} | StateTopType {} | StateTopCon {}, "use", pos) -> build innerBloc (StateUse {})

    -- If it does not break on "in", then it was actually a top-level type/con,
    -- and it must break the parent node.
    sem continue =
        | (StateType {} | StateCon {}, !"in") -> false

    -- If we find a breaker other than "in",
    -- we must trigger restructuring, as the inner assumption was false.
    sem reStructureTree =
        | (StateType {} | StateCon {}, !"in") -> true

    -- We only absorb "in"; other breakers are not part of the block.
    sem absorbIt =
        | (StateType {} | StateCon {}, "in") -> true

    -- If we break on anything other than "in",
    -- we cast the block as top-level.
    sem switchVersion =
        | (StateType {}, !"in") -> StateTopType {}
        | (StateCon {}, !"in") -> StateTopCon {}

end   

-- In this language we handle "lang" blocks.
-- Reminder: top-level keywords in lang blocks can only be:
-- sem, syn, con, type, and end (which closes the lang).
lang LangBreakerChooser = BreakerChooserInterface

    -- type, con, and syn have no nested blocks,
    -- so we can simply break on any top-level lang keyword.
    -- Sem is more complex, as it can contain nested blocks,
    -- and importantly, can contain type and con definitions.
    -- Therefore, we cannot immediately break on type/con,
    -- and must make assumptions.
    sem choose =
        | (StateLang {}, "type", pos) -> build langFullBreak (StateTopType {})
        | (StateLang {}, "con", pos) -> build langFullBreak (StateTopCon {})
        | (StateLang {}, "syn", pos) -> build langFullBreak (StateSyn {})
        
        | (StateLang {}, "sem", pos) -> build langBreak (StateSem {})

    -- lang only breaks on "end", which must be absorbed.
    sem absorbIt =
        | (StateLang {}, _) -> true

end


-- This language handles both syn and sem.
lang SemSynBreakerChooser = BreakerChooserInterface

    -- This implementation of choose may look confusing:
    -- - syn does not have any choose cases except use,
    --   because every opener syn could encounter is also a breaker of syn.
    -- - sem has 3 cases:
    --   1. let and utest are always inner blocks, so we treat them as inner.
    --      use also always closes with "in".
    --   2. type and con are ambiguous: we cannot know if they are top-level,
    --      so we assume they are not and allow them to break on "in".
    --   3. recursive is always an inner block, so it breaks on #in.
    sem choose =
        | (StateSem {}, "let", pos) -> build innerBloc (StateLet {})
        | (StateSem {}, "utest", pos) -> build innerBloc (StateUtest {})
        | (StateSem {} | StateSyn {}, "use", pos) -> build innerBloc (StateUse {})
        
        
        | (StateSem {}, "type", pos) -> build langFullBreakIn (StateType {})
        | (StateSem {}, "con", pos) -> build langFullBreakIn (StateCon {})

        | (StateSem {}, "recursive", pos) -> build recInner (StateRec {})

    -- We always continue the parent block (the lang),
    -- except if we break on "end", which is the breaker of lang.
    sem continue =
        | (StateSem {} | StateSyn {}, "end") -> false

end


-- Use is by far the simplest language, as it contains no nested blocks
-- and always breaks on "in".
-- No choose implementation is even needed.
lang UseBreakerChooser = BreakerChooserInterface

    -- We just want to absorb the "in" breaker.
    sem absorbIt =
        | (StateUse {}, "in") -> true
end


-- Final BreakerChooser unifying all the Breakers.    
lang BreakerChooser = ProgramBreakerChooser + RecBreakerChooser + LetUtestBreakerChooser + LangBreakerChooser + TypeConBreakerChooser + SemSynBreakerChooser + UseBreakerChooser + MexprBreakerChooser + LetRecBreakerChooser end
