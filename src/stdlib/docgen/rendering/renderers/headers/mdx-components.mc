include "string.mc"
include "./mdx-style.mc"

let mdxJsComponents =
join(["import React, { useMemo, useRef, useState, createContext, useContext } from 'react';
import \"./", mdxCssFileName, "\"

/** ------------------------------------------------------------------------------------
 *  Utils
 *  ---------------------------------------------------------------------------------- */
function slugify(input) {
  return input
    .toLowerCase()
    .replace(/[^a-z0-9]+/g, '-')
    .replace(/(^-|-$)/g, '');
}

/** ---------------------------------------------------------------------------------const Ctx = createContext(null);

/** ------------------------------------------------------------------------------------
 *  Badge
 *  ---------------------------------------------------------------------------------- */

export const Badge = ({ form }) => {
  if (!form) return null;
  return <span className=\"badge\">{form}</span>;
};

/** ------------------------------------------------------------------------------------
 *  DocBlock
 *  ---------------------------------------------------------------------------------- */

export const DocBlock = ({ title, form, link, children }) => {
  const [open, setOpen] = useState({});
  const anchorId = useMemo(() => slugify(title), [title]);

  return (
    <Ctx.Provider value={{ open, setOpen }}>
      <section id={anchorId} className=\"card\" aria-labelledby={`${anchorId}-title`}>
        <div className=\"header\">
          <h3 className=\"title\" id={`${anchorId}-title`}>
            <a href={`#${anchorId}`} className=\"anchor\">
              {title}
            </a>
          </h3>
          <Badge form={form} />
          <div className=\"spacer\"/>
          {link && (
            <a href={link} className=\"link\">→</a>
          )}
        </div>
        {children}
      </section>
    </Ctx.Provider>
  );
};

export const Description = ({ children }) => {
  if (!children) return null;
  return <div className=\"desc\">{children}</div>;
};

export const ToggleWrapper = ({ children, hiddenText, shownText }) => {
  const [visible, setVisible] = useState(false);

  return (
    <div>
      <button
        onClick={() => setVisible(!visible)}
        className=\"toggler\"
        aria-expanded={visible}
      >
        {visible ? shownText : hiddenText}
      </button>
      {visible && <span className=\"code\">{children}</span>}
    </div>
  );
};
"])


let mdxTsComponents =
join ["import React, { useMemo, useRef, useState, createContext, useContext } from 'react';
import \"./", mdxCssFileName, "\"

/** ------------------------------------------------------------------------------------
 *  Utils
 *  ---------------------------------------------------------------------------------- */
function slugify(input: string) {
  return input
    .toLowerCase()
    .replace(/[^a-z0-9]+/g, '-')
    .replace(/(^-|-$)/g, '');
}

function useId(prefix?: string) {
  const ref = useRef<string>();
  if (!ref.current) {
    const rnd = Math.random().toString(36).slice(2, 8);
   ref.current = `${prefix ?? 'docgen'}-${rnd}`;
  }
  return ref.current;
}

type PanelState = Record<string, boolean>;

type DocBlockCtx = {
  open: PanelState;
  setOpen: React.Dispatch<React.SetStateAction<PanelState>>;
};

const Ctx = createContext<DocBlockCtx | null>(null);
 
/** ------------------------------------------------------------------------------------
 *  Badge
 *  ---------------------------------------------------------------------------------- */

export const Badge: React.FC<{ form?: string }> = ({ form }) => {
  if (!form) return null;
  return <span className=\"badge\">{form}</span>;
};

/** ------------------------------------------------------------------------------------
 *  DocBlock
 *  ---------------------------------------------------------------------------------- */
type DocBlockProps = {
  title: string;
  form?: string;
  link?: string;
  children: React.ReactNode;
};

export const DocBlock: React.FC<DocBlockProps> = ({ title, form, link, children }) => {
  const [open, setOpen] = useState<PanelState>({});
  const anchorId = useMemo(() => slugify(title), [title]);

  return (
    <Ctx.Provider value={{ open, setOpen }}>
    <section id={anchorId} className=\"card\" aria-labelledby={`${anchorId}-title`}>
      <div className=\"header\">
        <h3 className=\"title\" id={`${anchorId}-title`}>
          <a href={`#${anchorId}`} className=\"anchor\">
            {title}
          </a>
        </h3>
        <Badge form={form} />
        <div className=\"spacer\" />
        {link && (
          <a href={link} className=\"link\">→</a>
        )}
      </div>
      {children}
    </section>
    </Ctx.Provider>
  );
};
  
export const Description: React.FC<{ children?: React.ReactNode }> = ({ children }) => {
  if (!children) return null;
  return <div className=\"desc\">{children}</div>;
};

type ToggleWrapperProps = { children: React.ReactNode };

export const ToggleWrapper: React.FC<ToggleWrapperProps> = ({ children, hiddenText, shownText }) => {
  const [visible, setVisible] = useState(false);

  return (
    <div>
      <button
        onClick={() => setVisible(!visible)}
        className=\"toggler\"
        aria-expanded={visible}
      >
        {visible ? shownText : hiddenText}
      </button>
      {visible && <span className=\"code\">{children}</span>}
    </div>
  );
};

"]
