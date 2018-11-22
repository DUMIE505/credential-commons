"use strict";var _stringify=require("babel-runtime/core-js/json/stringify"),_stringify2=_interopRequireDefault(_stringify),_getIterator2=require("babel-runtime/core-js/get-iterator"),_getIterator3=_interopRequireDefault(_getIterator2);function _interopRequireDefault(a){return a&&a.__esModule?a:{default:a}}var _=require("lodash"),timestamp=require("unix-timestamp"),sjcl=require("sjcl"),definitions=require("./definitions"),_require=require("../services"),services=_require.services,validIdentifiers=_.map(definitions,function(a){return a.identifier});function isValueOfType(a,b){return"String"===b?_.isString(a):"Number"===b?_.isNumber(a):!("Boolean"!=b)&&_.isBoolean(a)}function isValid(a,b,c){return"String"===b?(!c.pattern||c.pattern.test(a))&&(!c.minimumLength||a.length>=c.minimumLength)&&(!c.maximumLength||a.length<=c.minimumLength):"Number"===b?((!_.isNil(c.minimum)&&c.exclusiveMinimum?a>c.minimum:a>=c.minimum)||_.isNil(c.minimum))&&((!_.isNil(c.maximum)&&c.exclusiveMaximum?a<c.maximum:a<=c.maximum)||_.isNil(c.maximum)):!("Boolean"!=b)&&_.isBoolean(a)}var getTypeName=function a(b){if(_.isString(b.type)){if(_.includes(validIdentifiers,b.type)){var c=_.find(definitions,{identifier:b.type});return a(c)}return b.type}return"Object"},resolveType=function a(b){var c=getTypeName(b);if("Object"!==c)return c;if(!_.isString(b.type))return b.type;var d=_.find(definitions,{identifier:b.type});return a(d)},findDefinitionByAttestableValue=function a(b,c){var d=!0,e=!1,f=void 0;try{for(var g,h=(0,_getIterator3.default)(c.type.properties);!(d=(g=h.next()).done);d=!0){var i=g.value,j=_.find(definitions,{identifier:i.type});if(j.type=resolveType(j),!j.type.properties&&i.name===b)return i.type;if(j.type.properties)return a(b,j)}}catch(a){e=!0,f=a}finally{try{!d&&h.return&&h.return()}finally{if(e)throw f}}return null},getAllProperties=function a(b,c){var d=_.find(definitions,{identifier:b}),e=[],f=resolveType(d),g=_.isString(f)?_.find(definitions,{identifier:f}):d;if(g&&"Object"===getTypeName(g)){var h;if(g.type.properties)h=g.type.properties;else{var i=_.find(definitions,{identifier:g.type});h=resolveType(i).properties}var j=void 0,k=_.split(g.identifier,":");j=c?_.includes(c,_.lowerCase(k[1]))?c+"."+k[2]:c+"."+_.lowerCase(k[1])+"."+k[2]:_.lowerCase(k[1])+"."+k[2],_.includes(["String","Number","Boolean"],""+h.type)?e.push(j+"."+h.name):_.forEach(h,function(b){var c=_.split(b.type,":")[2],d=b.name===c?j:j+"."+b.name,f=a(b.type,d);_.forEach(f,function(a){return e.push(a)})})}else if(c){var l=c+"."+_.split(d.identifier,":")[2];e.push(l)}else{var m=_.split(b,":"),n=_.lowerCase(m[1])+"."+m[2];e.push(n)}return e},isAttestableValue=function(a){return a&&a.attestableValue},parseAttestableValue=function(a){var b=[],c=_.split(a.attestableValue,"|"),d=/^urn:(\w+(?:\.\w+)*):(\w+):(.+)/;if(_.each(c,function(a){var c=d.exec(a);if(c&&4===c.length){var e={propertyName:c[1],salt:c[2],value:c[3],stringValue:a};b.push(e)}}),c.length!==b.length&&c.length!==b.length+1)throw new Error("Invalid attestableValue");return b};function UCABaseConstructor(a,b,c){var d=this;if(this.timestamp=null,this.id=null,this.secureRandom=services.container.SecureRandom,!_.includes(validIdentifiers,a))throw new Error(a+" is not defined");this.identifier=a;var e=c?_.find(definitions,{identifier:a,version:c}):_.find(definitions,{identifier:a});if(this.version=c||e.version,this.type=getTypeName(e),e.type=resolveType(e),isAttestableValue(b)){var f=parseAttestableValue(b);if(1===f.length){this.timestamp=null,this.salt=f[0].salt;var g=f[0].value;this.value=_.includes(["null","undefined"],g)?null:g}else{for(var h={},j=function(a){var b=f[a].propertyName,c=b.split("."),d=c[c.length-2],g=d.substring(0,1).toUpperCase()+d.substring(1),i=c[c.length-1],j="cvc:"+g+":"+i,k=definitions.find(function(a){return a.identifier===j});k||(j=findDefinitionByAttestableValue(i,e)),h[b]=new UCABaseConstructor(j,{attestableValue:f[a].stringValue})},k=0;k<f.length;k+=1)j(k);this.value=h}}else if(isValueOfType(b,this.type)){if(this.timestamp=timestamp.now(),!isValid(b,this.type,e))throw new Error((0,_stringify2.default)(b)+" is not valid for "+a);this.value=b,this.salt=sjcl.codec.hex.fromBits(sjcl.hash.sha256.hash(this.secureRandom.wordWith(64)))}else if(_.isEmpty(e.type.properties))throw new Error((0,_stringify2.default)(b)+" is not valid for "+a);else{var l=_.reduce(e.type.required,function(a,c){return b[c]&&a},!0);if(!l)throw new Error("Missing required fields to "+a);var m=_.mapValues(_.keyBy(_.map(b,function(a,b){var c=_.find(e.type.properties,{name:b}),d=new UCABaseConstructor(c.type,a,c.version);return{key:b,value:d}}),"key"),"value");this.value=m}this.getAttestableValue=function(a){var b=d.identifier.lastIndexOf(":"),c=d.identifier.substring(b+1);switch(a&&(c=a+"."+c),d.type){case"String":return"urn:"+c+":"+d.salt+":"+d.value+"|";case"Number":return"urn:"+c+":"+d.salt+":"+d.value+"|";case"Boolean":return"urn:"+c+":"+d.salt+":"+d.value+"|";default:return _.reduce(_.sortBy(_.keys(d.value)),function(a,b){return""+a+d.value[b].getAttestableValue(c)},"");}},this.getGlobalCredentialItemIdentifier=function(){return"claim-"+d.identifier+"-"+d.version},this.getClaimRootPropertyName=function(){var a=_.split(d.identifier,":");return _.lowerCase(a[1])},this.getClaimPropertyName=function(){var a=_.split(d.identifier,":");return a[2]},this.getClaimPath=function(){var a=_.split(d.identifier,":"),b=_.lowerCase(a[1]);return b+"."+a[2]},this.getAttestableValues=function(){var a=[],b=_.find(definitions,{identifier:d.identifier,version:d.version});return(b.credentialItem||b.attestable)&&(a.push({identifier:d.identifier,value:d.getAttestableValue()}),"Object"===d.type&&_.forEach(_.keys(d.value),function(b){var c=d.value[b].getAttestableValues();_.reduce(c,function(a,b){return a.push(b)},a)})),a},this.getPlainValue=function(a){var b={},c=[];switch(d.type){case"String":case"Number":case"Boolean":if(a)b[a]=d.value;else{if(!d.credentialItem)return d.value;b[d.identifier]=d.value}return b;default:return _.forEach(_.sortBy(_.keys(d.value)),function(a){c.push(d.value[a].getPlainValue(a))}),_.forEach(c,function(c){a?(b[a]=b[a]?b[a]:{},_.assign(b[a],c)):_.assign(b,c)}),b;}};var n=sjcl.codec.hex.fromBits(sjcl.hash.sha256.hash(this.getAttestableValue()));return this.id=this.version+":"+this.identifier+":"+n,this}var UCA=UCABaseConstructor;function convertIdentifierToClassName(a){var b=_.split(a,":"),c=b[1],d=_.upperFirst(_.camelCase(b[2]));return""+c+d}_.forEach(_.filter(definitions,function(a){return a.credentialItem}),function(a){var b=convertIdentifierToClassName(a.identifier),c={},d=a.identifier;c[b]=function(a,b){var c=new UCABaseConstructor(d,a,b);return c},_.mixin(UCA,c)}),UCA.getTypeName=getTypeName,UCA.resolveType=resolveType,UCA.getAllProperties=getAllProperties,module.exports=UCA;