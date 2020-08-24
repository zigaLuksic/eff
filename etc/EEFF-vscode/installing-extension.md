# Install the extension

To start using the extension with Visual Studio Code copy it into the `<user home>/.vscode/extensions` folder and restart Code.

# Autocolor for EEFF files

Add the following your settings (JSON)
```
"files.associations": {
        "*.eff" : "eeff"
    }
```

# Setting token colors

The tokens are (probably) not recognized by your VSCode theme. To color the tokens add the following to your settings (JSON).
You need to change `[???]` to the name of your VSCode theme (e.g. `[Monokai Dimmed]`).
```
"editor.tokenColorCustomizations": {
    "[???]": {
        "textMateRules": [
            {
                "scope" : ["keyword.control.eeff"],
                "settings": {"foreground": "#5d9cd4",}
            },
            {
                "scope" : ["keyword.other.typedef.eeff"],
                "settings" : {"foreground" : "#aec977"}
            },
            {
                "scope" : ["constant.boolean.eeff", "constant.numeric.eeff"],
                "settings" : {"foreground" : "#aecfe2"}
            },
            {
                "scope" : ["symbol.theorysymbol.eeff", "symbol.typesymbol.eeff"],
                "settings" : {"foreground" : "#7f86c0"}
            },
            {
                "scope" : ["variable.constructor.eeff"],
                "settings" : {"foreground" : "#eec475"}
            },
            {
                "scope" : ["variable.invocation.eeff"],
                "settings" : {"foreground" : "#d8906e"}
            },
            {
                "scope" : ["comment.block.eeff"],
                "settings" : {"foreground" : "#9ba798"}
            },
            {
                "scope" : ["variable.typepar.eeff"],
                "settings" : {"foreground" : "#6fb38d"}
            }
        ]
    }
}
```