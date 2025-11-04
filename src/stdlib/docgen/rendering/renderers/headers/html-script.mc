let htmlScriptPath = "script.js"

let htmlScript: String =
"
function toggle(btn) {
    const scrollY = window.scrollY;
    const div = btn.nextElementSibling; 
    if (div.style.display === 'none') {
        div.style.display = 'inline';
    } else {
        div.style.display = 'none';
    }
    window.scrollTo({ top: scrollY });
}

const root = document.documentElement;
const button = document.getElementById(\"themeButton\");
const menu = document.getElementById(\"themeMenu\");

// Toggle the theme menu
button.addEventListener(\"click\", () => {
  menu.style.display = menu.style.display === \"none\" ? \"block\" : \"none\";
});

// Apply a theme when a theme button is clicked
menu.querySelectorAll(\"button\").forEach(btn => {
  btn.addEventListener(\"click\", () => {
    const theme = btn.dataset.theme;
    root.setAttribute(\"data-theme\", theme);
    button.textContent = \"Theme: \" + btn.textContent;
    menu.style.display = \"none\";
  });
});

// init label
button.textContent = \"Theme: Dark\";
root.setAttribute(\"data-theme\", \"htmlDark\");
"
