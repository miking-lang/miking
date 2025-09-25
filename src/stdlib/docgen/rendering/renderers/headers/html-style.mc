include "./theme-variables.mc"
include "./search.mc"

let htmlStylePath = "styles.css"

let htmlStyle: String = 
join [
themeVariables, "
/* =========================
   GENERIC STYLES (use vars)
   ========================= */

body {
  font-family: 'Segoe UI', Roboto, sans-serif;
  background-color: var(--bodyBGColor);
  color: var(--bodyTextColor);
  margin: 2rem auto;
  max-width: 960px;
  padding: 0 1rem;
  font-size: 16px;
  line-height: 1.7;
  letter-spacing: 0.02em;
}

h1 {
  font-size: 2.4em;
  font-weight: 700;
  border-bottom: 3px solid var(--h1BorderColor);
  padding-bottom: 0.4em;
  margin-bottom: 1.5em;
  color: var(--h1Color);
}

h2 {
  font-size: 1.8em;
  font-weight: 600;
  color: var(--h2Color);
  margin-top: 2.5em;
  border-left: 4px solid var(--h2BorderColor);
  padding-left: 0.6em;
}

pre {
  white-space: pre-wrap;
  overflow-wrap: break-word;
}

.top-doc {
  background-color: var(--topDocBgColor);
  border: 1px solid var(--topDocBorderColor);
  border-radius: 6px;
  padding: 1.5rem;
  margin-bottom: 2rem;
  line-height: 1.8;
  font-size: 0.96em;
  color: var(--topDocColor);
  box-shadow: 0 2px 4px rgba(0, 0, 0, 0.4);
}

.top-doc pre {
  margin-top: 0.5em;
  margin-bottom: 0.5em;
}

.top-doc code {
  padding: 0.2em 0.4em;
  border-radius: 3px;
  font-family: monospace;
  font-size: 0.95em;
}

.doc-block {
  background-color: var(--docBlockBGColor);
  border-left: 3px solid var(--docBlockBorderColor);
  border: 1px solid var(--docBlockOutlineColor);
  border-radius: 4px;
  padding: 0.8rem 1rem;
  margin: 1.5rem 0;
  font-size: 15px;
  position: relative;
}

.doc-signature {
  background-color: var(--docSignatureBGColor);
  padding: 0.4em 0.8em;
  border-radius: 3px;
  font-weight: 600;
  display: inline-block;
  margin-bottom: 0.6em;
}

.doc-description {
  background-color: var(--docDescriptionBGColor);
  padding: 0.5em 1em;
  color: var(--docDescriptionTextColor);
  font-style: italic;
  font-size: 0.95em;
  margin-bottom: 0.5em;
  white-space: pre-wrap;
  word-wrap: break-word;
  overflow-wrap: break-word;
}

.code-block {
  background-color: var(--codeBlockBGColor);
  border: 1px solid var(--codeBlockBorderColor);
  border-radius: 4px;
  padding: 0.5em 0.8em;
  margin-top: 0.5em;
  font-family: monospace;
  font-size: 0.9em;
}

.toggle-btn {
  all: unset;
  border: none;
  padding: 0.2em 0.5em;
  font-size: 0.85em;
  font-family: monospace;
  cursor: pointer;
  transition: background-color 0.2s ease;
}

.toggle-btn:hover {
  background-color: var(--toggleHoverBGColor);
}

.hiden-code {}

.gotoLink {
  font-size: 1.1em;
  color: var(--gotoLinkColor);
  text-decoration: none;
  position: absolute;
  top: 0.6em;
  right: 1em;
  opacity: 0.7;
  font-weight: 500;
  transition: opacity 0.2s ease, transform 0.2s ease;
}

a {
  color: var(--aColor);
  text-decoration: none;
  font-size: 1.05em;
  font-weight: 500;
  transition: color 0.2s ease, text-decoration 0.2s ease;
}

a:hover {
  text-decoration: underline;
}

.gotoLink:hover {
  opacity: 1;
  transform: scale(1.1);
}

", searchCss, "

.kw      { color: var(--keywordColor); font-weight: 500; }
.var     { color: var(--variableColor); }
.tp      { color: var(--typeColor); }
.number  { color: var(--numberColor); }
.comment { color: var(--commentColor); font-style: italic; }
.string  { color: var(--stringColor); }
.multi   { color: var(--multiColor); }

.theme-toggle {
  position: fixed;
  top: 10px;
  right: 10px;
  padding: 0.4em 0.8em;
  border: 1px solid var(--topDocBorderColor);
  border-radius: 6px;
  font-size: 0.85em;
  font-weight: 500;
  background: var(--docSignatureBGColor);
  color: var(--bodyTextColor);
  cursor: pointer;
  transition: background-color 0.2s ease, opacity 0.2s ease;
  z-index: 1100;
}

.theme-toggle:hover {
  background: var(--toggleHoverBGColor);
  opacity: 0.9;
}

/* Dropdown container */
#themeMenu {
  position: fixed;
  top: 55px;   /* just below the button */
  right: 10px;
  display: none; /* toggled by JS */
  background: var(--topDocBgColor);
  border: 1px solid var(--topDocBorderColor);
  border-radius: 6px;
  box-shadow: 0 4px 8px rgba(0,0,0,0.15);
  padding: 0.4em;
  z-index: 1000;
}

/* Theme option buttons */
#themeMenu button {
  display: block;
  width: 100%;
  padding: 0.4em 0.8em;
  margin: 0.2em 0;
  border: none;
  border-radius: 4px;
  background: var(--docSignatureBGColor);
  color: var(--bodyTextColor);
  cursor: pointer;
  font-size: 0.95em;
  text-align: left;
  transition: background-color 0.2s ease;
}

#themeMenu button:hover {
  background: var(--toggleHoverBGColor);
}
"]
