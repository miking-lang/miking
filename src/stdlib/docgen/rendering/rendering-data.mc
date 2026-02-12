include "../global/objects.mc"

type RenderingData = use Objects in {
    obj: Object,

    split: Int,
    code: String,

    tests: String
}

let renderingDataNew : use Objects in Object -> String -> Int -> String -> RenderingData =
    lam obj. lam code. lam split. lam tests.
    {
        split = split,
        obj = obj,
        tests = tests,
        code = code
    }

let renderingDataLeft : RenderingData -> String =
    lam data.
    match splitAt data.code data.split with (left, _) in left

let renderingDataLeft : RenderingData -> String =
    lam data.
    match splitAt data.code data.split with (_, right) in right
