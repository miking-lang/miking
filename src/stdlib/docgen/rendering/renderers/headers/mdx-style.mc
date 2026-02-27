let mdxCssFileName = "style.css"

let mdxCss = 
"
.card {
  border: 1px solid var(--docgen-border, #e5e7eb);
  border-radius: 10px;
  padding: 0.6rem 0.8rem;
  margin-bottom: 30px;
  position: relative;
  box-shadow: 0 1px 2px rgba(0,0,0,.04);
  transition: box-shadow .15s ease, transform .15s ease, border-color .15s ease;
  will-change: transform;
}

.header {
  display: flex;
  align-items: baseline;
  gap: 0.8rem;
  flex-wrap: nowrap;
  margin-bottom: 0.8rem;
}

.title {
  font-size: 1.12rem;
  font-weight: 700;
  letter-spacing: .2px;
  color: var(--docgen-text, #111827);
  line-height: 1;
}

.badge {
  display: inline-flex;
  align-items: center;
  font-size: 0.72rem;
  line-height: 1;
  padding: 0.18rem 0.55rem;
  border-radius: 9999px;
  border: 1px solid var(--docgen-accent, #3b82f6);
  background: var(
    --docgen-badge-bg,
    color-mix(in srgb, var(--docgen-accent, #3b82f6) 8%, transparent)
  );
  color: var(--docgen-accent, #3b82f6);
  text-transform: uppercase;
  letter-spacing: .3px;
}

.desc {
  padding-left: 0.8em;
  color: var(--docgen-muted, #6b7280);
  white-space: pre-wrap;
  line-height: 1.65;
  overflow: auto;
}

.spacer {
  flex: 1;
}

.link {
  display: inline-flex;
  align-items: center;
  gap: 0.25rem;
  font-size: 1.1rem;
  font-weight: 500;
  color: var(--docgen-accent, #3b82f6);
  text-decoration: none;
  cursor: pointer;
  transition: color 0.2s ease;
}

.code {
  text-align: left;
  font-family: var(
    --ifm-font-family-monospace,
    ui-monospace,
    SFMono-Regular,
    Menlo,
    Monaco,
    Consolas,
    \"Liberation Mono\",
    \"Courier New\",
    monospace
  );
  font-size: 0.93rem;
  line-height: 1.35;
  padding-bottom: 0;
  margin-bottom: 0;
  margin-left: 0.5rem;
  tab-size: 2;
}

.toggler {
  display: inline-flex;
  align-items: baseline;
  vertical-align: baseline;

  font-size: 0.7em;
  background: transparent;
  border: none;
  color: var(--docgen-accent, #3b82f6);
  cursor: pointer;
  padding: 0.15rem 0.3rem;
  border-radius: 4px;
  transition: background 0.2s ease;
}


.toggler:hover {
  background: rgba(59,130,246,0.1);
}

.anchor {
  color: inherit;
  text-decoration: none;
  position: relative;
}

.anchor:hover::after {
  content: \"#\";
  position: absolute;
  left: -1.2rem;
  opacity: 0.6;
}

.doc-signature {
  display: inline-block;
  flex-direction: column;
  align-items: flex-start;
  gap: 0.4rem;
  background-color: #f5f5f5f5;
  padding: 0.4em 0.9em;
  border-radius: 3px;
  box-sizing: border-box;
  margin-bottom: 0.6em;
  overflow: auto;

  width: 100%;
}

.doc-signature > div {
  display: inline;
}

.variants {
  display: block;
  overflow: auto;
  width: 100%;
  margin-top: 0.4rem;
}

.variant {
  white-space: nowrap;
}

.kw      { color: #d73a49; }
.var     { color: #1d1d1f; }
.tp      { color: #6f42c1; }
.number  { color: #005cc5; }
.comment { color: #6a737d; font-style: italic; }
.string  { color: #032f62; }
.multi   { color: #22863a; }
"
