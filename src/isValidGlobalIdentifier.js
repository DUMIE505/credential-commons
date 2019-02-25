import includes from 'lodash/includes';
import map from 'lodash/map';
import split from 'lodash/split';

const { definitions } = require('@identity.com/uca');
const vcDefinitions = require('./creds/definitions');
const claimDefinitions = require('./claim/definitions');


const validUCAIdentifiers = map(definitions, d => d.identifier);
const validClaimIdentifiers = map(claimDefinitions, d => d.identifier);
const validVCIdentifiers = map(vcDefinitions, d => d.identifier);
const validPrefixes = ['claim', 'credential'];

function isValidGlobalIdentifier(identifier) {
  const splited = split(identifier, '-');

  if (splited.length !== 3) {
    throw new Error('Malformed Global Identifier');
  }

  if (!includes(validPrefixes, splited[0])) {
    throw new Error('Invalid Global Identifier Prefix');
  }

  switch (splited[0]) {
    case 'claim':
      if (!includes(validUCAIdentifiers, splited[1]) && !includes(validClaimIdentifiers, identifier)) {
        throw new Error(`${identifier} is not valid`);
      }
      return true;
    case 'credential':
      if (!includes(validVCIdentifiers, splited[1]) && !includes(validVCIdentifiers, identifier)) {
        throw new Error(`${identifier} is not valid`);
      }
      return true;
    default:
      return false;
  }
}

module.exports = isValidGlobalIdentifier;
