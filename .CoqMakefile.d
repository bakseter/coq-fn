theories/Syntax.vo theories/Syntax.glob theories/Syntax.v.beautified theories/Syntax.required_vo: theories/Syntax.v 
theories/Syntax.vio: theories/Syntax.v 
theories/Syntax.vos theories/Syntax.vok theories/Syntax.required_vos: theories/Syntax.v 
theories/Semantics.vo theories/Semantics.glob theories/Semantics.v.beautified theories/Semantics.required_vo: theories/Semantics.v theories/Syntax.vo
theories/Semantics.vio: theories/Semantics.v theories/Syntax.vio
theories/Semantics.vos theories/Semantics.vok theories/Semantics.required_vos: theories/Semantics.v theories/Syntax.vos
theories/Parser.vo theories/Parser.glob theories/Parser.v.beautified theories/Parser.required_vo: theories/Parser.v theories/Syntax.vo theories/Semantics.vo
theories/Parser.vio: theories/Parser.v theories/Syntax.vio theories/Semantics.vio
theories/Parser.vos theories/Parser.vok theories/Parser.required_vos: theories/Parser.v theories/Syntax.vos theories/Semantics.vos
theories/Examples.vo theories/Examples.glob theories/Examples.v.beautified theories/Examples.required_vo: theories/Examples.v theories/Syntax.vo theories/Semantics.vo theories/Parser.vo
theories/Examples.vio: theories/Examples.v theories/Syntax.vio theories/Semantics.vio theories/Parser.vio
theories/Examples.vos theories/Examples.vok theories/Examples.required_vos: theories/Examples.v theories/Syntax.vos theories/Semantics.vos theories/Parser.vos
