include "./theme-variables.mc"
include "string.mc"
include "seq.mc"

let searchHtml: String = 
"<div id=\"search-container\">
  <input id=\"search-bar\" type=\"text\" placeholder=\"Type to search [r]\" />
  <div id=\"search-results\"></div>
</div>"

let searchCss: String = 
"
/* Search Engine */
#search-container {
    padding: 15px;
    display: flex;
    justify-content: center;
    position: relative;
}

#search-bar {
    width: 60%;
    max-width: 600px;
    padding: 10px 14px;
    font-size: 15px;
    border: none;
    border-radius: 3px;
    background: var(--searchBarBGColor);
    color: var(--searchBarTextColor);
    box-shadow: inset 0 1px 2px var(--searchBarShadowColor);
}

#search-bar::placeholder {
    color: var(--searchBarPlaceholderColor);
}

#search-results {
    position: absolute;
    top: 100%;
    left: 50%;
    transform: translateX(-50%);
    width: 60%;
    max-width: 600px;
    display: flex;
    flex-direction: column;
    gap: 6px;
    z-index: 1000;
    border-radius: 6px;
    padding: 6px 0;
    box-shadow: 0 4px 12px var(--searchResultsShadowColor);
}

#search-results a:first-child {
    margin-top: 0;
}

#search-bar:focus {
    outline: none;
}

#search-results a {
    display: flex;
    align-items: center;
    padding: 10px 14px;
    border-radius: 6px;
    color: var(--searchResultItemTextColor);
    background: var(--searchResultBGColor);
    backdrop-filter: blur(6px);
    font-size: 15px;
    margin: 0;
    transition: background 0.2s, transform 0.15s;
}

#search-results a + a {
    border-top: 1px solid var(--searchResultItemBorderColor);
}

#search-results a:hover {
    background: var(--searchResultItemHoverBGColor);
    transform: translateX(4px);
    cursor: pointer;
}

#search-results a:active {
    background: var(--searchResultItemActiveBGColor);
    transform: translateX(2px);
}

#search-results a {
    white-space: nowrap;
    overflow: hidden;
    text-overflow: ellipsis;
}

.highlight {
    font-weight: bold;
    color: var(--searchHighlightColor);
    white-space: nowrap;
}

"

let searchCore: String =
"
export function filterResults(results, query) {
  if (!query || query.trim().length === 0) return [];

  const normalized = query.trim().toLowerCase();

  return results
    .filter(word => word.name.toLowerCase().includes(normalized))
    .sort((a, b) => a.name.length - b.name.length)
    .slice(0, 10);
}

export function highlightMatch(text, query) {
  if (!query) return text;
  const regex = new RegExp(`(${query})`, \"gi\");
  return text.replace(regex, \"<span class='highlight'>$1</span>\");
}
"

let searchPath : String -> String = concat "Search"

type SearchDictObj = { name: String, link: String }

let buildDict : [SearchDictObj] -> String = lam objects.
    strJoin ",\n" (map (lam obj.
        join ["{ name: \"", obj.name, "\", link: \"", obj.link, "\" }"]
    ) objects)

let searchReact: [SearchDictObj] -> String = lam objects.
  let dict = buildDict objects in
join [
"
import React, { useState, useEffect, useRef } from 'react';

", searchCore, "

const results = [", dict, "];

const searchCss = `
", mdxSearchVariables, "
", searchCss, "
`;

export default function Search() {
  const [query, setQuery] = useState(\"\");
  const [open, setOpen] = useState(false);
  const containerRef = useRef(null);
  const inputRef = useRef(null);

  useEffect(() => {
    // inject CSS
    const style = document.createElement(\"style\");
    style.textContent = searchCss;
    document.head.appendChild(style);

    // force light theme
    document.documentElement.setAttribute(\"data-theme\", \"htmlLight\");

    return () => {
      style.remove();
    };
  }, []);

  useEffect(() => {
    // close on outside click
    function handleClickOutside(event) {
      if (containerRef.current && !containerRef.current.contains(event.target)) {
        setOpen(false);
      }
    }
    document.addEventListener(\"mousedown\", handleClickOutside);
    return () => document.removeEventListener(\"mousedown\", handleClickOutside);
  }, []);

  useEffect(() => {
    // global keybinding: 'r' focuses search
    function handleKeyPress(event) {
      if (event.key === 'r') {
        inputRef.current?.focus();
      }
    }
    document.addEventListener(\"keypress\", handleKeyPress);
    return () => document.removeEventListener(\"keypress\", handleKeyPress);
  }, []);

  const processInput = (value) => {
    const q = value.trim();
    setQuery(value);
    setOpen(q.length > 0);
    return filterResults(results, q);
  };

  const candidates = filterResults(results, query);

  return (
    <div
      id=\"search-container\"
      ref={containerRef}
      className=\"relative w-full max-w-md mx-auto\"
    >
      <input
        id=\"search-bar\"
        ref={inputRef}
        type=\"text\"
        value={query}
        placeholder=\"Type to search [r]\"
        className=\"w-full rounded-2xl border border-gray-300 bg-white px-4 py-2 shadow-sm focus:border-blue-500 focus:ring-2 focus:ring-blue-400 focus:outline-none\"
        onChange={(e) => processInput(e.target.value)}
        onFocus={(e) => processInput(e.target.value)}
        onKeyDown={(e) => {
          if (e.key === \"Enter\") {
            e.preventDefault();
            if (candidates.length > 0) {
              window.location.href = candidates[0].link;
            }
          }
        }}
      />
      {open && candidates.length > 0 && (
        <div
          id=\"search-results\"
          className=\"absolute z-10 mt-2 w-full rounded-2xl bg-white shadow-lg border border-gray-200\"
        >
          {candidates.map((c) => (
            <a
              key={c.link}
              href={c.link}
              className=\"block px-4 py-2 text-gray-700 hover:bg-blue-50 hover:text-blue-600 transition-colors duration-150\"
              dangerouslySetInnerHTML={{
                __html: highlightMatch(c.name, query),
              }}
            ></a>
          ))}
        </div>
      )}
    </div>
  );
}
"
]

let searchJs: [SearchDictObj] -> String = lam objects.
let dict = buildDict objects in
join [
"
const results = [", dict, "];   

const searchBar = document.getElementById(\"search-bar\");
const resultsDiv = document.getElementById(\"search-results\");

let inputProcess = () => {
    const query = searchBar.value.trim();
    resultsDiv.innerHTML = \"\";

    if (query.length === 0) return;

    const candidates = results
        .filter(word => word.name.includes(query))
        .sort((a, b) => a.name.length - b.name.length)
        .slice(0, 10);

    const regex = new RegExp(`(${query})`, \"gi\");

    const frag = document.createDocumentFragment();

    for (const candidate of candidates) {
        const choice = document.createElement(\"a\");
        choice.innerHTML = candidate.name.replace(regex, \"<span class='highlight'>$1</span>\");
        choice.href = candidate.link;
        frag.appendChild(choice);
    }

    resultsDiv.appendChild(frag);

    return candidates;
};


document.addEventListener(\"keypress\", (event) => {
    if (event.key === 'r') {
        searchBar.focus();
    }
});

searchBar.addEventListener(\"keydown\", (event) => {
    if (event.key === \"Enter\") {
        event.preventDefault();
        const candidates = inputProcess() || [];
        if (candidates.length > 0) {
            window.location.href = candidates[0].link;
        }
    }
});
searchBar.addEventListener(\"input\", inputProcess);
searchBar.addEventListener(\"focus\", inputProcess);
document.addEventListener(\"mousedown\", (event) => {
  if (!searchBar.contains(event.target) && !resultsDiv.contains(event.target)) {
    resultsDiv.innerHTML = \"\";
  }
});
"]
