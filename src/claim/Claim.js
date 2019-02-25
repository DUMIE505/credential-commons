import map from 'lodash/map';
import split from 'lodash/split';
import find from 'lodash/find';
import includes from 'lodash/includes';
import each from 'lodash/each';
import reduce from 'lodash/reduce';
import sortBy from 'lodash/sortBy';
import keys from 'lodash/keys';
import camelCase from 'lodash/camelCase';
import forEach from 'lodash/forEach';
import isString from 'lodash/isString';
import lowerCase from 'lodash/lowerCase';
import upperFirst from 'lodash/upperFirst';
import filter from 'lodash/filter';
import mixin from 'lodash/mixin';

const sjcl = require('sjcl');
const { UserCollectableAttribute } = require('@identity.com/uca');
const definitions = require('./definitions');
const { services } = require('../services');

const validIdentifiers = map(definitions, d => d.identifier);

function getBaseIdentifiers(identifier) {
  const claimRegex = /claim-cvc:(.*)\.(.*)-v\d*/;
  let isNewIdentifier = true;

  let identifierComponents = claimRegex.exec(identifier);
  if (identifierComponents === null) {
    identifierComponents = split(identifier, ':');
    isNewIdentifier = false;
  }
  return { identifierComponents, isNewIdentifier };
}

function adaptIdentifierIfNeeded(identifier) {
  const { isNewIdentifier, identifierComponents } = getBaseIdentifiers(identifier);

  if (!isNewIdentifier && !find(definitions, { identifier })) {
    const newIdentifier = `claim-cvc:${identifierComponents[1]}.${identifierComponents[2]}-v1`;
    const foundNewIdentifier = find(definitions, { identifier: newIdentifier });
    if (foundNewIdentifier) {
      return newIdentifier;
    }
    throw new Error(`${identifier} is not defined`);
  }
  return identifier;
}

class Claim extends UserCollectableAttribute {
  constructor(identifier, value, version) {
    const currentIdentifier = adaptIdentifierIfNeeded(identifier);
    super(currentIdentifier, value, version, definitions);
    this.initialize(currentIdentifier, value, version);
  }

  initialize(identifier, value, version) {
    super.initialize(identifier, value, version);
    if (!this.salt) {
      const secureRandom = services.container.SecureRandom;
      this.salt = sjcl.codec.hex.fromBits(sjcl.hash.sha256.hash(secureRandom.wordWith(64)));
    }
  }

  initializeAttestableValue() {
    const { value } = this;
    const definition = this.version
      ? find(definitions, { identifier: this.identifier, version: this.version })
      : find(definitions, { identifier: this.identifier });

    // Trying to construct UCA with a existing attestableValue
    const parsedAttestableValue = Claim.parseAttestableValue(value);
    if (parsedAttestableValue.length === 1) {
      // This is a simple attestableValue
      this.timestamp = null;
      this.salt = parsedAttestableValue[0].salt;
      const ucaValue = parsedAttestableValue[0].value;
      this.value = includes(['null', 'undefined'], ucaValue) ? null : ucaValue;
    } else {
      const ucaValue = {};
      for (let i = 0; i < parsedAttestableValue.length; i += 1) {
        const { propertyName } = parsedAttestableValue[i];
        // we have stored only the property name on the urn, so we have to find the UCA definition
        const splitPropertyName = propertyName.split('.');
        // this property is used to check if the recursion tree has more than an depth
        const ucaNamespace = splitPropertyName[splitPropertyName.length - 2];
        const ucaNamespacePascal = ucaNamespace.substring(0, 1).toUpperCase() + ucaNamespace.substring(1);
        const ucaPropertyName = splitPropertyName[splitPropertyName.length - 1];
        let filteredIdentifier = `cvc:${ucaNamespacePascal}:${ucaPropertyName}`;
        // test if definition exists
        const filteredDefinition = definitions.find(def => def.identifier === filteredIdentifier);
        if (!filteredDefinition) {
          // this must have an claim path with no recursive definition
          filteredIdentifier = this.findDefinitionByAttestableValue(ucaPropertyName, definition);
        }
        ucaValue[propertyName] = new Claim(filteredIdentifier,
          { attestableValue: parsedAttestableValue[i].stringValue });
      }
      this.value = ucaValue;
    }
  }

  /* eslint-disable class-methods-use-this */
  getValidIdentifiers() {
    return validIdentifiers;
  }

  static resolveType(definition) {
    return UserCollectableAttribute.resolveType(definition, definitions);
  }

  static parseAttestableValue(value) {
    const values = [];
    const splitPipes = split(value.attestableValue, '|');
    const attestableValueRegex = /^urn:(\w+(?:\.\w+)*):(\w+):(.+)/;
    each(splitPipes, (stringValue) => {
      const match = attestableValueRegex.exec(stringValue);
      if (match && match.length === 4) {
        const v = {
          propertyName: match[1],
          salt: match[2],
          value: match[3],
          stringValue,
        };
        values.push(v);
      }
    });
    if (splitPipes.length !== values.length && splitPipes.length !== values.length + 1) {
      throw new Error('Invalid attestableValue');
    }
    return values;
  }

  findDefinitionByAttestableValue(attestableValuePropertyName, rootDefinition) {
    // eslint-disable-next-line no-restricted-syntax
    for (const property of rootDefinition.type.properties) {
      const resolvedDefinition = find(definitions, { identifier: property.type });
      resolvedDefinition.type = UserCollectableAttribute.resolveType(resolvedDefinition, definitions);
      if (!resolvedDefinition.type.properties && property.name === attestableValuePropertyName) {
        return property.type;
      }
      if (resolvedDefinition.type.properties) {
        return this.findDefinitionByAttestableValue(attestableValuePropertyName, resolvedDefinition);
      }
    }
    return null;
  }

  getAttestableValue(path) {
    // all UCA properties they have the form of :propertyName or :something.propertyName
    const { identifierComponents } = getBaseIdentifiers(this.identifier);
    let propertyName = identifierComponents[2];
    if (path) {
      propertyName = `${path}.${propertyName}`;
    }

    // it was defined that the attestable value would be on the URN type https://tools.ietf.org/html/rfc8141
    if (['String', 'Number', 'Boolean'].indexOf(this.type) >= 0) {
      return `urn:${propertyName}:${this.salt}:${this.value}|`;
    }
    return reduce(sortBy(keys(this.value)),
      (s, k) => `${s}${this.value[k].getAttestableValue(propertyName)}`, '');
  }

  /**
   * Returns the global CredentialItem of the Credential
   */
  getGlobalIdentifier() {
    return `claim-${this.identifier}-${this.version}`;
  }

  getClaimRootPropertyName() {
    const { identifierComponents } = getBaseIdentifiers(this.identifier);
    return camelCase(identifierComponents[1]);
  }

  getClaimPropertyName() {
    const { identifierComponents } = getBaseIdentifiers(this.identifier);
    return identifierComponents[2];
  }

  getClaimPath() {
    return Claim.getPath(this.identifier);
  }

  static getPath(identifier) {
    const { identifierComponents } = getBaseIdentifiers(identifier);
    const baseName = camelCase(identifierComponents[1]);
    return `${baseName}.${identifierComponents[2]}`;
  }

  getAttestableValues() {
    const values = [];
    const def = find(definitions, { identifier: this.identifier, version: this.version });
    if (def.credentialItem || def.attestable) {
      values.push({ identifier: this.identifier, value: this.getAttestableValue() });
      if (this.type === 'Object') {
        forEach(keys(this.value), (k) => {
          const innerValues = this.value[k].getAttestableValues();
          reduce(innerValues, (res, iv) => res.push(iv), values);
        });
      }
    }
    return values;
  }

  /**
   * extract the expected Type name for the value when constructing an UCA
   * @param {*} definition
   */
  static getTypeName(definition) {
    if (isString(definition.type)) {
      if (includes(validIdentifiers, definition.type)) {
        const innerDefinition = find(definitions, { identifier: definition.type });
        return this.getTypeName(innerDefinition);
      }

      return definition.type;
    }
    return 'Object';
  }

  static getAllProperties(identifier, pathName) {
    const definition = find(definitions, { identifier });
    const properties = [];
    const type = UserCollectableAttribute.resolveType(definition, definitions);
    const typeDefinition = isString(type) ? find(definitions, { identifier: type }) : definition;

    if (typeDefinition && this.getTypeName(typeDefinition) === 'Object') {
      let typeDefProps;
      if (typeDefinition.type.properties) {
        typeDefProps = typeDefinition.type.properties;
      } else {
        const typeDefDefinition = find(definitions, { identifier: typeDefinition.type });
        typeDefProps = UserCollectableAttribute.resolveType(typeDefDefinition, definitions).properties;
      }

      let basePropName;
      const { identifierComponents: baseIdentifierComponents } = getBaseIdentifiers(identifier);
      if (pathName) {
        if (includes(pathName, lowerCase(baseIdentifierComponents[1]))) {
          basePropName = `${pathName}`;
        } else {
          basePropName = `${pathName}.${lowerCase(baseIdentifierComponents[1])}.${baseIdentifierComponents[2]}`;
        }
      } else {
        basePropName = `${lowerCase(baseIdentifierComponents[1])}.${baseIdentifierComponents[2]}`;
      }

      if (includes(['String', 'Number', 'Boolean'], `${typeDefProps.type}`)) {
        // Properties is not an object
        properties.push(`${basePropName}.${typeDefProps.name}`);
      } else {
        forEach(typeDefProps, (prop) => {
          const { isNewIdentifier } = getBaseIdentifiers(prop.type);
          const newBasePropName = !isNewIdentifier ? basePropName : `${basePropName}.${prop.name}`;
          const proProperties = this.getAllProperties(prop.type, newBasePropName);
          forEach(proProperties, p => properties.push(p));
        });
      }
    } else if (pathName) {
      const { identifierComponents } = getBaseIdentifiers(definition.identifier);
      let propertiesName;
      if (pathName.indexOf(identifierComponents[2]) >= 0) {
        propertiesName = `${pathName}`;
      } else {
        propertiesName = `${pathName}.${identifierComponents[2]}`;
      }
      properties.push(propertiesName);
    } else {
      const { identifierComponents } = getBaseIdentifiers(identifier);
      const propertiesName = `${lowerCase(identifierComponents[1])}.${identifierComponents[2]}`;
      properties.push(propertiesName);
    }
    return properties;
  }
}

function convertIdentifierToClassName(identifier) {
  const { identifierComponents } = getBaseIdentifiers(identifier);
  const baseName = identifierComponents[1];
  const detailName = upperFirst(camelCase(identifierComponents[2]));
  return `${baseName}${detailName}`;
}

function mixinIdentifiers(UCA) {
  // Extend UCA Semantic
  forEach(filter(definitions, d => d.credentialItem), (def) => {
    const name = convertIdentifierToClassName(def.identifier);
    const source = {};
    const { identifier } = def;

    function UCAConstructor(value, version) {
      const self = new Claim(identifier, value, version);
      return self;
    }

    source[name] = UCAConstructor;
    mixin(Claim, source);
  });
  return UCA;
}

module.exports = { Claim: mixinIdentifiers(Claim), definitions, getBaseIdentifiers };
