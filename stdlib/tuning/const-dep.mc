include "mexpr/ast.mc"

-- Language fragment that describes how data- and execution time dependencies
-- flow from input parameters to the result for constants.

let _constDepData = (true,false)
let _constDepExe = (false,true)
let _constDepBoth = (true,true)
let _constDepNone = (false,false)

lang IntDep = IntAst
  sem constDep =
  | CInt _ -> []
end

lang ArithIntDep = ArithIntAst
  sem constDep =
  | CAddi _ -> [_constDepData, _constDepData]
  | CSubi _ -> [_constDepData, _constDepData]
  | CMuli _ -> [_constDepData, _constDepData]
  | CDivi _ -> [_constDepData, _constDepData]
  | CNegi _ -> [_constDepData]
  | CModi _ -> [_constDepData]
end

lang ShiftIntDep = ShiftIntAst
  sem constDep =
  | CSlli _ -> [_constDepData]
  | CSrli _ -> [_constDepData]
  | CSrai _ -> [_constDepData]
end

lang FloatDep = FloatAst
  sem constDep =
  | CFloat _ -> []
end

lang ArithFloatDep = ArithFloatAst
  sem constDep =
  | CAddf _ -> [_constDepData, _constDepData]
  | CSubf _ -> [_constDepData, _constDepData]
  | CMulf _ -> [_constDepData, _constDepData]
  | CDivf _ -> [_constDepData, _constDepData]
  | CNegf _ -> [_constDepData]
end

lang FloatIntConversionDep = FloatIntConversionAst
  sem constDep =
  | CFloorfi _ -> [_constDepData]
  | CCeilfi _ -> [_constDepData]
  | CRoundfi _ -> [_constDepData]
  | CInt2float _ -> [_constDepData]
end

lang BoolDep = BoolAst
  sem constDep =
  | CBool _ -> []
end

lang CmpIntDep = CmpIntAst
  sem constDep =
  | CEqi _ -> [_constDepData, _constDepData]
  | CNeqi _ -> [_constDepData, _constDepData]
  | CLti _ -> [_constDepData, _constDepData]
  | CGti _ -> [_constDepData, _constDepData]
  | CLeqi _ -> [_constDepData, _constDepData]
  | CGeqi _ -> [_constDepData, _constDepData]
end

lang CmpFloatDep = CmpFloatAst
  sem constDep =
  | CEqf _ -> [_constDepData, _constDepData]
  | CLtf _ -> [_constDepData, _constDepData]
  | CLeqf _ -> [_constDepData, _constDepData]
  | CGtf _ -> [_constDepData, _constDepData]
  | CGeqf _ -> [_constDepData, _constDepData]
  | CNeqf _ -> [_constDepData, _constDepData]
end

lang CharDep = CharAst
  sem constDep =
  | CChar _ -> []
end

lang CmpCharDep = CmpCharAst
  sem constDep =
  | CEqc _ -> [_constDepData, _constDepData]
end

lang IntCharConversionDep = IntCharConversionAst
  sem constDep =
  | CInt2Char _ -> [_constDepData]
  | CChar2Int _ -> [_constDepData]
end

lang FloatStringConversionDep = FloatStringConversionAst
  sem constDep =
  -- NOTE(Linnea,2021-11-19): technically, the execution times of these
  -- conversions depend on the length of the strings, but we ignore that for
  -- now.
  | CStringIsFloat _ -> [_constDepData]
  | CString2float _ -> [_constDepData]
  | CFloat2string _ -> [_constDepData]
end

lang SymbDep = SymbAst
  sem constDep =
  | CSymb _ -> []
  | CGensym _ -> [_constDepNone]
  | CSym2hash _ -> [_constDepData]
end

lang CmpSymbDep = CmpSymbAst
  sem constDep =
  | CEqsym _ -> [_constDepData, _constDepData]
end

lang SeqOpDep = SeqOpAst
  -- TODO(Linnea,2021-11-22): Does not handle different behaviors for Rope and
  -- List. E.g., concat is linear for list but not for Rope. Moreover,
  -- operations that are O(1) for both might have different constants. E.g.,
  -- perhaps 'cons' should have execution dep. and not just data.
  sem constDep =
  -- NOTE(Linnea,2021-11-19): Assumes that the execution time of set and get
  -- depends on the index.
  | CSet _ -> [_constDepBoth, _constDepData, _constDepBoth]
  | CGet _ -> [_constDepBoth, _constDepBoth]
  | CCons _ -> [_constDepData, _constDepData] -- NOTE(Linnea,2021-11-22): Assumes O(1)
  | CSnoc _ -> [_constDepData, _constDepData] -- NOTE(Linnea,2021-11-22): Assumes O(1)
  | CConcat _ -> [_constDepData, _constDepData] -- NOTE(Linnea,2021-11-22): Assumes O(1)
  | CLength _ -> [_constDepData] -- NOTE(Linnea,2021-11-22): Assumes O(1)
  | CReverse _ -> [_constDepBoth] -- NOTE(Linnea,2021-11-22): Assumes > O(1)
  | CHead _ -> [_constDepData] -- NOTE(Linnea,2021-11-22): Assumes O(1)
  | CTail _ -> [_constDepData] -- NOTE(Linnea,2021-11-22): Assumes O(1)
  | CNull _ -> [_constDepData] -- NOTE(Linnea,2021-11-22): Assumes O(1)
  | CMap _ -> [_constDepBoth, _constDepBoth]
  | CMapi _ -> [_constDepBoth, _constDepBoth]
  | CIter _ -> [_constDepExe, _constDepExe]
  | CIteri _ -> [_constDepExe, _constDepExe]
  | CFoldl _ -> [_constDepBoth, _constDepBoth, _constDepBoth]
  | CFoldr _ -> [_constDepBoth, _constDepBoth, _constDepBoth]
  | CCreate _ -> [_constDepBoth, _constDepBoth]
  | CCreateList _ -> [_constDepBoth, _constDepBoth]
  | CCreateRope _ -> [_constDepData, _constDepBoth]  -- NOTE(Linnea,2021-11-22): Assumes length does not affect creation time of Rope
  | CIsList _ -> [_constDepData]
  | CIsRope _ -> [_constDepData]
  | CSplitAt _ -> [_constDepBoth, _constDepBoth]
  | CSubsequence _ -> [_constDepBoth, _constDepBoth, _constDepBoth]
end

lang FileOpDep = FileOpAst
  sem constDep =
  | CFileRead _ -> [_constDepBoth]
  | CFileWrite _ -> [_constDepNone, _constDepExe]
  | CFileExists _ -> [_constDepData]
  | CFileDelete _ -> [_constDepNone]
end

lang IODep = IOAst
  sem constDep =
  | CPrint _ -> [_constDepNone]
  | CPrintError _ -> [_constDepNone]
  | CDPrint _ -> [_constDepNone]
  | CFlushStdout _ -> [_constDepNone]
  | CFlushStderr _ -> [_constDepNone]
  | CReadLine _ -> [_constDepNone]
  | CReadBytesAsString _ -> [_constDepData]
end

lang RandomNumberGeneratorDep = RandomNumberGeneratorAst
  sem constDep =
  | CRandIntU _ -> [_constDepData,_constDepData]
  | CRandSetSeed _ -> [_constDepNone]
end

lang SysDep = SysAst
  sem constDep =
  | CExit _ -> [_constDepNone]
  | CError _ -> [_constDepNone]
  | CArgv _ -> []
  | CCommand _ -> [_constDepBoth]
end

lang TimeDep = TimeAst
  sem constDep =
  | CWallTimeMs _ -> [_constDepNone]
  | CSleepMs _ -> [_constDepExe]
end

lang ConTagDep = ConTagAst
  sem constDep =
  | CConstructorTag _ -> [_constDepData]
end

-- NOTE(Linnea, 2021-11-22): This is not sufficient for tracking data flow of
-- references. For example:
--   let r = ref <data1> in
--   let r2 = r in
--   modref r2 <data2> in
--   let x = deref r in  <-- {data1} ⊆ x, {data2} ⊈ x
lang RefOpDep = RefOpAst
  sem constDep =
  | CRef _ -> [_constDepData]
  | CModRef _ -> [_constDepNone,_constDepNone]
  | CDeRef _ -> [_constDepData]
end

-- NOTE(Linnea, 2021-11-22): Assumes that all elements take equal time to
-- insert, delete, or find.
lang MapDep = MapAst
  sem constDep =
  | CMapEmpty _ -> [_constDepData]
  | CMapInsert _ -> [_constDepData,_constDepData,_constDepBoth]
  | CMapRemove _ -> [_constDepData,_constDepBoth]
  | CMapFindExn _ -> [_constDepData,_constDepBoth]
  | CMapFindOrElse _ -> [_constDepBoth,_constDepData,_constDepBoth]
  | CMapFindApplyOrElse _ -> [_constDepBoth,_constDepBoth,_constDepData,_constDepBoth]
  | CMapBindings _ -> [_constDepBoth]
  | CMapChooseExn _ -> [_constDepData] -- NOTE(Linnea, 2021-11-22): Assuming O(1).
  | CMapChooseOrElse _ -> [_constDepBoth,_constDepData]
  | CMapSize _ -> [_constDepBoth] -- NOTE(Linnea, 2021-11-22): Assuming O(n).
  | CMapMem _ -> [_constDepData,_constDepBoth]
  | CMapAny _ -> [_constDepBoth,_constDepBoth]
  | CMapMap _ -> [_constDepBoth,_constDepBoth]
  | CMapMapWithKey _ -> [_constDepBoth,_constDepBoth]
  | CMapFoldWithKey _ -> [_constDepBoth,_constDepBoth,_constDepBoth] -- NOTE(Linnea, 2021-11-22): Assuming accumulator's start value affects execution time, which it does in the general case, but perhaps not so often in practice.
  | CMapEq _ -> [_constDepBoth,_constDepBoth,_constDepBoth]
  | CMapCmp _ -> [_constDepBoth,_constDepBoth,_constDepBoth]
  | CMapGetCmpFun _ -> [_constDepData] -- NOTE(Linnea, 2021-11-22): Implies that
                                       -- a data dependency that entered through
                                       -- an element in the map may
                                       -- "contaminate" the compare function.
end

lang TensorOpDep = TensorOpAst
  sem constDep =
  | CTensorCreateInt _ -> error "TensorOpDep not implemented yet"
  | CTensorCreateFloat _ -> error "TensorOpDep not implemented yet"
  | CTensorCreate _ -> error "TensorOpDep not implemented yet"
  | CTensorGetExn _ -> error "TensorOpDep not implemented yet"
  | CTensorSetExn _ -> error "TensorOpDep not implemented yet"
  | CTensorRank _ -> error "TensorOpDep not implemented yet"
  | CTensorShape _ -> error "TensorOpDep not implemented yet"
  | CTensorReshapeExn _ -> error "TensorOpDep not implemented yet"
  | CTensorCopy _ -> error "TensorOpDep not implemented yet"
  | CTensorTransposeExn _ -> error "TensorOpDep not implemented yet"
  | CTensorSliceExn _ -> error "TensorOpDep not implemented yet"
  | CTensorSubExn _ -> error "TensorOpDep not implemented yet"
  | CTensorIterSlice _ -> error "TensorOpDep not implemented yet"
  | CTensorEq _ -> error "TensorOpDep not implemented yet"
  | CTensorToString _ -> error "TensorOpDep not implemented yet"
end

lang BootParserDep = BootParserAst
  sem constDep =
  | CBootParserParseMExprString _ -> error "BootParserDep not implemented yet"
  | CBootParserParseMCoreFile _ -> error "BootParserDep not implemented yet"
  | CBootParserGetId _ -> error "BootParserDep not implemented yet"
  | CBootParserGetTerm _ -> error "BootParserDep not implemented yet"
  | CBootParserGetType _ -> error "BootParserDep not implemented yet"
  | CBootParserGetString _ -> error "BootParserDep not implemented yet"
  | CBootParserGetInt _ -> error "BootParserDep not implemented yet"
  | CBootParserGetFloat _ -> error "BootParserDep not implemented yet"
  | CBootParserGetListLength _ -> error "BootParserDep not implemented yet"
  | CBootParserGetConst _ -> error "BootParserDep not implemented yet"
  | CBootParserGetPat _ -> error "BootParserDep not implemented yet"
  | CBootParserGetInfo _ -> error "BootParserDep not implemented yet"
end

lang MExprConstDep =
  IntDep + ArithIntDep + ShiftIntDep + FloatDep + ArithFloatDep +
  FloatIntConversionDep + BoolDep + CmpIntDep + CmpFloatDep +
  CharDep + CmpCharDep + IntCharConversionDep +
  FloatStringConversionDep + SymbDep + CmpSymbDep + SeqOpDep +
  FileOpDep + IODep + RandomNumberGeneratorDep + SysDep + TimeDep +
  ConTagDep + RefOpDep + MapDep + TensorOpDep + BootParserDep

mexpr

use MExprConstDep in

utest constDep (CInt {val = 0}) with [] in
utest constDep (CAddi {}) with [_constDepData,_constDepData] in

()
