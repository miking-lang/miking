# JavaScript `web` Tests
> By William Rågstad - 2022/08/07.

The `web` target is telling the compiler to generate JS code intended to be used in a web browser. This is hard to automate testing for.
This folder contains a Node.js application that emulates execution in a web browser.
It uses the [`jsdom`](https://github.com/jsdom/jsdom) library to create a virtual DOM as well as a headless browser.

The `make.sh` script is used to run tests through a more user-friendly interface,
and is hooked up to the automated testing system in GitHub Actions.

## Adding a new test
To add a new test, create a new `.mc` file in the `test/js/web` folder.
All tests in this folder should test the functionality of the different external library functions supported by the `web` target,
e.g. functions such as `getDocument`, `getElementById`, and so on from the `javascript/web/dom-api-ext.mc` file.

Because there is no way of testing Miking code that uses external libraries from the `web` target, all tests should instead be compiled to JavaScript in form of `mexpr` with a set of `utest`.

For example:

`test.mc`

```lua
mexpr
	let doc = getDocument () in
	utest eqString doc.location.hostname "" with false in
()
```
> Again, we cannot run this with `mi` or `boot` because it uses external libraries that are only available when compiling to JavaScript for the `web` target.

This will be compiled to JavaScript and all tests are runned in a headless browser.
