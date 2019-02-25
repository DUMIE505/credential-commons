import endsWith from 'lodash/endsWith';
import map from 'lodash/map';
import find from 'lodash/find';
import includes from 'lodash/includes';
import each from 'lodash/each';
import reduce from 'lodash/reduce';
import keys from 'lodash/keys';
import forEach from 'lodash/forEach';
import get from 'lodash/get';
import filter from 'lodash/filter';
import clone from 'lodash/clone';
import ceil from 'lodash/ceil';
import merge from 'lodash/merge';
import concat from 'lodash/concat';
import isEmpty from 'lodash/isEmpty';
import remove from 'lodash/remove';
import unset from 'lodash/unset';
import set from 'lodash/set';
import cloneDeep from 'lodash/cloneDeep';
import indexOf from 'lodash/indexOf';
import findLastIndex from 'lodash/findLastIndex';
import lastIndexOf from 'lodash/lastIndexOf';
import isNil from 'lodash/isNil';
import isFunction from 'lodash/isFunction';
import pick from 'lodash/pick';
import difference from 'lodash/difference';
import fromPairs from 'lodash/fromPairs';
import sortBy from 'lodash/sortBy';
import toPairs from 'lodash/toPairs';

const sift = require('sift');
const MerkleTools = require('merkle-tools');
const sjcl = require('sjcl');
const timestamp = require('unix-timestamp');
const flatten = require('flat');
const uuidv4 = require('uuid/v4');
const { Claim } = require('../claim/Claim');
const definitions = require('./definitions');
const { services } = require('../services');

function sha256(string) {
  return sjcl.codec.hex.fromBits(sjcl.hash.sha256.hash(string));
}

function getClaimPath(identifier, claimsPathRef) {
  const sufix = Claim.getPath(identifier);
  const claimPath = find(claimsPathRef, o => endsWith(o, sufix));
  return claimPath || sufix;
}

function validIdentifiers() {
  const vi = map(definitions, d => d.identifier);
  return vi;
}

function getClaimsWithFlatKeys(claims) {
  const flattenDepth3 = flatten(claims, { maxDepth: 3 });
  const flattenDepth2 = flatten(claims, { maxDepth: 2 });
  const flattenClaim = merge({}, flattenDepth3, flattenDepth2);
  const flattenSortedKeysClaim = fromPairs(sortBy(toPairs(flattenClaim)));
  return flattenSortedKeysClaim;
}


function paths(root) {
  const pathsArray = [];
  const nodes = [{
    obj: root,
    path: [],
  }];
  while (nodes.length > 0) {
    const n = nodes.pop();
    Object.keys(n.obj).forEach((k) => {
      if (typeof n.obj[k] === 'object') {
        const path = n.path.concat(k);
        pathsArray.push(path);
        nodes.unshift({
          obj: n.obj[k],
          path,
        });
      }
    });
  }
  const returnArray = [];
  pathsArray.forEach((arr) => {
    returnArray.push(arr.join('.'));
  });
  return returnArray;
}

function getLeavesClaimPaths(signLeaves) {
  return map(signLeaves, 'claimPath');
}

function verifyLeave(leave, merkleTools, claims, signature, invalidValues, invalidHashs, invalidProofs) {
  // 1. verify valid targetHashs
  // 1.1 "leave.value" should be equal claim values
  const ucaValue = new Claim(leave.identifier, { attestableValue: leave.value });
  if (ucaValue.type === 'String' || ucaValue.type === 'Number') {
    if (ucaValue.value !== get(claims, leave.claimPath)) {
      invalidValues.push(leave.value);
    }
  } else if (ucaValue.type === 'Object') {
    const ucaValueValue = ucaValue.value;
    const claimValue = get(claims, leave.claimPath);
    const ucaValueKeys = keys(ucaValue.value);
    each(ucaValueKeys, (k) => {
      const expectedClaimValue = claimValue[k];
      if (expectedClaimValue && get(ucaValueValue[k], 'value') !== expectedClaimValue) {
        invalidValues.push(claimValue[k]);
      }
    });
  } else {
    // Invalid ucaValue.type
    invalidValues.push(leave.value);
  }

  // 1.2 hash(leave.value) should be equal leave.targetHash
  const hash = sha256(leave.value);
  if (hash !== leave.targetHash) invalidHashs.push(leave.targetHash);

  // 2. Validate targetHashs + proofs with merkleRoot
  const isValidProof = merkleTools.validateProof(leave.node, leave.targetHash, signature.merkleRoot);
  if (!isValidProof) invalidProofs.push(leave.targetHash);
}

/**
 * Transform DSR constraints to sift constraits
 * @param {*} constraints
 */
function transformConstraint(constraints) {
  const resultConstraints = [];

  forEach(constraints.claims, (constraint) => {
    if (!constraint.path) {
      throw new Error('Malformed contraint: missing PATTH');
    }
    if (!constraint.is) {
      throw new Error('Malformed contraint: missing IS');
    }

    const siftConstraint = {};
    siftConstraint[constraint.path] = constraint.is;
    resultConstraints.push(siftConstraint);
  });

  return resultConstraints;
}

/**
 * Transforms a list of UCAs into the signature property of the verifiable claims
 */
class CvcMerkleProof {
  static get PADDING_INCREMENTS() {
    return 16;
  }

  constructor(ucas, claimsPathRef) {
    const withRandomUcas = CvcMerkleProof.padTree(ucas);
    this.type = 'CvcMerkleProof2018';
    this.merkleRoot = null;
    this.anchor = 'TBD (Civic Blockchain Attestation)';
    this.leaves = CvcMerkleProof.getAllAttestableValue(withRandomUcas);
    this.buildMerkleTree(claimsPathRef);
  }

  buildMerkleTree(claimsPathRef) {
    const merkleTools = new MerkleTools();
    const hashes = map(this.leaves, n => sha256(n.value));
    merkleTools.addLeaves(hashes);
    merkleTools.makeTree();
    forEach(hashes, (hash, idx) => {
      this.leaves[idx].claimPath = getClaimPath(this.leaves[idx].identifier, claimsPathRef);
      this.leaves[idx].targetHash = hash;
      this.leaves[idx].node = merkleTools.getProof(idx);
    });
    this.leaves = filter(this.leaves, el => !(el.identifier === 'cvc:Random:node'));
    this.merkleRoot = merkleTools.getMerkleRoot().toString('hex');
  }

  static padTree(nodes) {
    const currentLength = nodes.length;
    const targetLength = currentLength < CvcMerkleProof.PADDING_INCREMENTS ? CvcMerkleProof.PADDING_INCREMENTS
      : ceil(currentLength / CvcMerkleProof.PADDING_INCREMENTS) * CvcMerkleProof.PADDING_INCREMENTS;
    const newNodes = clone(nodes);
    const secureRandom = services.container.SecureRandom;
    while (newNodes.length < targetLength) {
      newNodes.push(new Claim('cvc:Random:node', secureRandom.wordWith(16)));
    }
    return newNodes;
  }

  static getAllAttestableValue(ucas) {
    const values = [];
    forEach(ucas, (uca) => {
      const innerValues = uca.getAttestableValues();
      reduce(innerValues, (res, iv) => {
        res.push(iv);
        return res;
      }, values);
    });
    return values;
  }
}
/**
 * Transforms a list of UCAs into the claim property of the verifiable cliams
 */
class ClaimModel {
  constructor(ucas) {
    forEach(ucas, (uca) => {
      const rootPropertyName = uca.getClaimRootPropertyName();
      if (!this[rootPropertyName]) {
        this[rootPropertyName] = {};
      }
      this[rootPropertyName][uca.getClaimPropertyName()] = uca.getPlainValue();
    });
  }
}

const VERIFY_LEVELS = {
  INVALID: -1, // Verifies if the VC structure and/or signature proofs is not valid, or credential is expired
  PROOFS: 0, // Verifies if the VC structure  and/or signature proofs are valid, including the expiry
  ANCHOR: 1, // Verifies if the VC Attestation Anchor structure is valid
  GRANTED: 2, // Verifies if the owner granted the VC usage for a specific request
  BLOCKCHAIN: 3, // Verifies if the VC Attestation is valid on the blockchain
};

/**
 * Creates a new Verifiable Credential based on an well-known identifier and it's claims dependencies
 * @param {*} identifier
 * @param {*} issuer
 * @param {*} ucas
 * @param {*} version
 */
function VerifiableCredentialBaseConstructor(identifier, issuer, expiryIn, ucas, version) {
  this.id = uuidv4();
  this.issuer = issuer;
  const issuerUCA = new Claim('cvc:Meta:issuer', this.issuer);
  this.issuanceDate = (new Date()).toISOString();
  const issuanceDateUCA = new Claim('cvc:Meta:issuanceDate', this.issuanceDate);
  this.identifier = identifier;
  this.expirationDate = expiryIn ? timestamp.toDate(timestamp.now(expiryIn)).toISOString() : null;
  const expiryUCA = new Claim('cvc:Meta:expirationDate', this.expirationDate ? this.expirationDate : 'null');

  const proofUCAs = expiryUCA ? concat(ucas, issuerUCA, issuanceDateUCA, expiryUCA)
    : concat(ucas, issuerUCA, issuanceDateUCA);

  if (!includes(validIdentifiers(), identifier)) {
    throw new Error(`${identifier} is not defined`);
  }

  const definition = version ? find(definitions, { identifier, version: `${version}` })
    : find(definitions, { identifier });
  if (!definition) {
    throw new Error(`Credential definition for ${identifier} v${version} not found`);
  }
  this.version = `${version}` || definition.version;
  this.type = ['Credential', identifier];

  // ucas can be empty here if it is been constructed from JSON
  if (!isEmpty(ucas)) {
    this.claim = new ClaimModel(ucas);
    const claimsPathRef = paths(this.claim);
    const deepKeys = keys(flatten(this.claim, { safe: true }));
    const allClaimsPaths = claimsPathRef.concat(deepKeys);
    this.proof = new CvcMerkleProof(proofUCAs, allClaimsPaths);
    if (!isEmpty(definition.excludes)) {
      const removed = remove(this.proof.leaves, el => includes(definition.excludes, el.identifier));
      forEach(removed, (r) => {
        unset(this.claim, r.claimPath);
      });
    }
    // The VC Grantted session (see .grantUsageFor)
    this.granted = null;
  }

  /**
   * Returns the global identifier of the Credential
   */
  this.getGlobalIdentifier = () => (`credential-${this.identifier}-${this.version}`);

  /**
   * Creates a filtered credential exposing only the requested claims
   * @param {*} requestedClaims
   */
  this.filter = (requestedClaims) => {
    const filtered = cloneDeep(this);
    remove(filtered.proof.leaves, el => !includes(requestedClaims, el.identifier));

    filtered.claim = {};
    forEach(filtered.proof.leaves, (el) => {
      set(filtered.claim, el.claimPath, get(this.claim, el.claimPath));
    });

    return filtered;
  };

  /**
   * Request that this credential MerkleRoot is anchored on the Blockchain.
   * This will return a _temporary_ anchor meaning that the blockchain entry is still not confirmed.
   *
   * @param options options to be passed
   * @param options.subject the local signed subject with the user private key
   * @param options.subject.label a short description of the subject
   * @param options.subject.data hash of the merkle root
   * @param options.subject.pub xpub of the signing private key
   * @param options.subject.signature the value of the signature of the private key
   * @param options.network testnet for test env, bitcoin for production
   * @param options.cosigner object containing private and public key for cosigning
   * @param options.cosigner.xpub public key of the cosigner
   * @param options.cosigner.xprv private key of the cosigner
   *
   * @returns the json object containing the whole anchor attestation
   *
   */
  this.requestAnchor = async (options) => {
    const anchorService = services.container.AnchorService;
    const updatedOption = merge({},
      options,
      {
        subject: {
          label: this.identifier,
          data: this.proof.merkleRoot,
        },
      });
    const anchor = await anchorService.anchor(updatedOption);
    this.proof.anchor = anchor;
    return this;
  };

  /**
   * Trys to renew the current anchor. replecinf the _temporary_ anchor for a _permanent_ one,
   * already confirmed on the blockchain.
   */
  this.updateAnchor = async () => {
    const anchorService = services.container.AnchorService;
    const anchor = await anchorService.update(this.proof.anchor);
    this.proof.anchor = anchor;
    return this;
  };

  /**
   * Iterate over all leaves and see if their proofs are valid
   * @returns {boolean}
   */
  this.verifyProofs = () => {
    const expiry = clone(this.expirationDate);
    const claims = clone(this.claim);
    const signature = clone(this.proof);
    const signLeaves = get(signature, 'leaves');
    let valid = false;

    const merkleTools = new MerkleTools();
    const claimsWithFlatKeys = getClaimsWithFlatKeys(claims);
    const leavesClaimPaths = getLeavesClaimPaths(signLeaves);
    const invalidClaim = [];
    const invalidExpiry = [];
    const invalidValues = [];
    const invalidHashs = [];
    const invalidProofs = [];
    forEach(keys(claimsWithFlatKeys), (claimKey) => {
      // check if `claimKey` has a `claimPath` proof
      const leaveIdx = indexOf(leavesClaimPaths, claimKey);
      // if not found
      if (leaveIdx === -1) {
        // .. still test if parent key node may have a `claimPath` proof
        findLastIndex(claimKey, '.');
        const parentClaimKey = claimKey.substring(0, lastIndexOf(claimKey, '.'));
        if (indexOf(leavesClaimPaths, parentClaimKey) > -1) {
          // if yes, no problem, go to next loop
          return;
        }
        // if no, include on invalidClaim array
        invalidClaim.push(claimKey);
      } else {
        const leave = signLeaves[leaveIdx];
        verifyLeave(leave, merkleTools, claims, signature, invalidValues, invalidHashs, invalidProofs);
      }
    });

    // It has to be present Credential expiry even with null value
    const expiryIdx = indexOf(leavesClaimPaths, 'meta.expirationDate');
    if (expiryIdx >= 0) {
      const expiryLeave = signLeaves[expiryIdx];
      const metaClaim = {
        meta: {
          expirationDate: expiry,
        },
      };
      const totalLengthBefore = invalidValues.length + invalidHashs.length + invalidProofs.length;
      verifyLeave(expiryLeave, merkleTools, metaClaim, signature, invalidValues, invalidHashs, invalidProofs);
      const totalLengthAfter = invalidValues.length + invalidHashs.length + invalidProofs.length;
      if (totalLengthAfter === totalLengthBefore) {
        // expiry has always to be string formatted date or null value
        // if it is null it means it's indefinitely
        if (expiry !== null) {
          const now = new Date();
          const expiryDate = new Date(expiry);
          if (now.getTime() > expiryDate.getTime()) {
            invalidExpiry.push(expiry);
          }
        }
      }
    }
    if (isEmpty(invalidClaim)
        && isEmpty(invalidValues)
        && isEmpty(invalidHashs)
        && isEmpty(invalidProofs)
        && isEmpty(invalidExpiry)) {
      valid = true;
    }
    return valid;
  };

  /**
   * Verify the Credential and return a verification level.
   * @return Any of VC.VERIFY_LEVELS
   */
  this.verify = (higherVerifyLevel, options) => {
    const { requestorId, requestId, keyName } = options || {};
    const hVerifyLevel = !isNil(higherVerifyLevel) ? higherVerifyLevel : VERIFY_LEVELS.GRANTED;
    let verifiedlevel = VERIFY_LEVELS.INVALID;

    // Test next level
    if (verifiedlevel === VERIFY_LEVELS.INVALID
        && hVerifyLevel >= VERIFY_LEVELS.PROOFS
        && this.verifyProofs()) verifiedlevel = VERIFY_LEVELS.PROOFS;

    // Test next level
    if (verifiedlevel === VERIFY_LEVELS.PROOFS
        && hVerifyLevel >= VERIFY_LEVELS.ANCHOR
        && this.verifyAttestation()) verifiedlevel = VERIFY_LEVELS.ANCHOR;

    // Test next level
    if (verifiedlevel === VERIFY_LEVELS.ANCHOR
        && hVerifyLevel >= VERIFY_LEVELS.GRANTED
        && this.verifyGrant(requestorId, requestId, keyName)) verifiedlevel = VERIFY_LEVELS.GRANTED;

    return verifiedlevel;
  };

  /**
   * This method checks if the signature matches for the root of the Merkle Tree
   * @return true or false for the validation
   */
  this.verifySignature = async () => services.container.AnchorService.verifySignature(this.proof);

  /**
   * This method checks that the attestation / anchor exists on the BC
   */
  this.verifyAttestation = async () => services.container.AnchorService.verifyAttestation(this.proof);

  /**
   * This method will revoke the attestation on the chain
   * @returns {Promise<Promise<*>|void>}
   */
  this.revokeAttestation = async () => services.container.AnchorService.revokeAttestation(this.proof);

  /**
   * This method will check on the chain the balance of the transaction and if it's still unspent, than it's not revoked
   * @returns {Promise<Promise<*>|void>}
   */
  this.isRevoked = async () => services.container.AnchorService.isRevoked(this.proof);

  this.isMatch = (constraints) => {
    const siftConstraints = transformConstraint(constraints);
    let result = true;

    forEach(siftConstraints, (constraint) => {
      result = (sift.indexOf(constraint, [this.claim]) > -1);
      return result;
    });
    return result;
  };

  /**
   * Updates the credential with a "granted" token based on the requestorId and a unique requestId (a nonce) that
   * can be verified later using .verify() function.
   *
   * @param  {string} requestorId - The IDR id (DID).
   * @param  {string} requestId - A unique requestID. This should be a nonce for proof chanlange.
   * @param  {Object} option - You should provide either a keyName or a pvtKey.
   * @param  {string} option.keyName - A keyName - if CryptoManager is been used.
   * @param  {string} option.pvtKey - A pvtKey in base58 format (default impl).
   */
  this.grantUsageFor = (requestorId, requestId, { keyName, pvtKey }) => {
    if (isEmpty(get(this.proof, 'anchor.subject.label')) || isEmpty(get(this.proof, 'anchor.subject.pub'))) {
      throw new Error('Invalid credential attestation/anchor');
    }
    if (!this.verifySignature()) {
      throw new Error('Invalid credential attestation/anchor signature');
    }
    if (!requestorId || !requestId || !(keyName || pvtKey)) {
      throw new Error('Missing required parameter: requestorId, requestId or key');
    }
    // eslint-disable-next-line max-len
    const stringToHash = `${this.proof.anchor.subject.label}${this.proof.anchor.subject.data}${requestorId}${requestId}`;
    const hexHash = sha256(stringToHash);

    const cryptoManager = services.container.CryptoManager;

    let signKey = keyName;
    if (pvtKey) {
      if (!isFunction(cryptoManager.installKey)) {
        throw new Error('You provide a `pvtKey` but the CryptoManager does not support it, use a `keyName` instead.');
      }
      signKey = `TEMP_KEY_NAME_${new Date().getTime()}`;
      cryptoManager.installKey(signKey, pvtKey);
    }

    const hexSign = cryptoManager.sign(signKey, hexHash);
    this.granted = hexSign;
  };

  /**
   * @param  {} requestorId
   * @param  {} requestId
   * @param  {} [keyName]
   */
  this.verifyGrant = (requestorId, requestId, keyName) => {
    let verified = false;
    if (isEmpty(get(this.proof, 'anchor.subject.label')) || isEmpty(get(this.proof, 'anchor.subject.pub'))) {
      return verified;
    }
    if (isEmpty(this.granted)) {
      return verified;
    }
    if (!requestorId || !requestId) {
      return verified;
    }
    // eslint-disable-next-line max-len
    const stringToHash = `${this.proof.anchor.subject.label}${this.proof.anchor.subject.data}${requestorId}${requestId}`;
    const hexHash = sha256(stringToHash);

    const cryptoManager = services.container.CryptoManager;

    let verifyKey = keyName;
    if (isEmpty(verifyKey)) {
      if (!isFunction(cryptoManager.installKey)) {
        throw new Error('CryptoManager does not support intallKey, please use a `keyName` instead.');
      }
      verifyKey = `TEMP_KEY_NAME_${new Date().getTime()}`;
      const anchorPubKey = get(this.proof, 'anchor.subject.pub');
      cryptoManager.installKey(verifyKey, anchorPubKey);
    }
    verified = cryptoManager.verify(verifyKey, hexHash, this.granted);
    return verified;
  };

  return this;
}


/**
 * CREDENTIAL_META_FIELDS - Array with meta fields of a credential
 */
const CREDENTIAL_META_FIELDS = [
  'id',
  'identifier',
  'issuer',
  'issuanceDate',
  'expirationDate',
  'version',
  'type',
];

/**
 *
 * @param {*} vc
 */
const getCredentialMeta = vc => pick(vc, CREDENTIAL_META_FIELDS);

/**
 *
 * @param {*} constraintsMeta
 */
function transformMetaConstraint(constraintsMeta) {
  const resultConstraints = [];

  // handle special field constraints.meta.credential
  // const constraintsMetaCredential = get(constraintsMeta, 'meta.credential');
  // if (constraintsMetaCredential) {
  //   return { identifier: constraintsMetaCredential };
  // }
  const constraintsMetaKeys = keys(constraintsMeta.meta);
  forEach(constraintsMetaKeys, (constraintKey) => {
    const constraint = constraintsMeta.meta[constraintKey];
    const siftConstraint = {};
    // handle special field constraints.meta.credential
    if (constraintKey === 'credential') {
      siftConstraint.identifier = constraint;
    } else if (constraint.is) {
      siftConstraint[constraintKey] = constraint.is;
    } else {
      throw new Error(`Malformed meta contraint "${constraintKey}": missing the IS`);
    }
    resultConstraints.push(siftConstraint);
  });
  return resultConstraints;
}

/**
 * isMatchCredentialMeta
 * @param {*} credentialMeta A Object continais only VC meta fields. Other object keys will be ignored.
 * @param {*} constraintsMeta Example:
 * // constraints.meta = {
 * //   "credential": "credential-civ:Credential:CivicBasic-1",
 * //   "issuer": {
 * //     "is": {
 * //       "$eq": "did:ethr:0xaf9482c84De4e2a961B98176C9f295F9b6008BfD"
 * //     }
 * //   }
 */
const isMatchCredentialMeta = (credentialMeta, constraintsMeta) => {
  const siftConstraints = transformMetaConstraint(constraintsMeta);
  let result = !isEmpty(siftConstraints) && true;
  forEach(siftConstraints, (constraint) => {
    result = (sift.indexOf(constraint, [credentialMeta]) > -1) && result;
  });
  return result;
};

VerifiableCredentialBaseConstructor.CREDENTIAL_META_FIELDS = CREDENTIAL_META_FIELDS;
VerifiableCredentialBaseConstructor.getCredentialMeta = getCredentialMeta;
VerifiableCredentialBaseConstructor.isMatchCredentialMeta = isMatchCredentialMeta;

/**
 * Factory function that creates a new Verifiable Credential based on a JSON object
 * @param {*} verifiableCredentialJSON
 */
VerifiableCredentialBaseConstructor.fromJSON = (verifiableCredentialJSON) => {
  const newObj = new VerifiableCredentialBaseConstructor(verifiableCredentialJSON.identifier,
    verifiableCredentialJSON.issuer);
  newObj.id = clone(verifiableCredentialJSON.id);
  newObj.issuanceDate = clone(verifiableCredentialJSON.issuanceDate);
  newObj.expirationDate = clone(verifiableCredentialJSON.expirationDate);
  newObj.identifier = clone(verifiableCredentialJSON.identifier);
  newObj.version = clone(verifiableCredentialJSON.version);
  newObj.type = cloneDeep(verifiableCredentialJSON.type);
  newObj.claim = cloneDeep(verifiableCredentialJSON.claim);
  newObj.proof = cloneDeep(verifiableCredentialJSON.proof);
  newObj.granted = clone(verifiableCredentialJSON.granted) || null;
  return newObj;
};

/**
 * List all properties of a Verifiable Credential
 */
VerifiableCredentialBaseConstructor.getAllProperties = (identifier) => {
  const vcDefinition = find(definitions, { identifier });
  if (vcDefinition) {
    const allProperties = [];
    forEach(vcDefinition.depends, (ucaIdentifier) => {
      allProperties.push(...Claim.getAllProperties(ucaIdentifier));
    });
    const excludesProperties = [];
    forEach(vcDefinition.excludes, (ucaIdentifier) => {
      excludesProperties.push(...Claim.getAllProperties(ucaIdentifier));
    });
    return difference(allProperties, excludesProperties);
  }
  return null;
};

VerifiableCredentialBaseConstructor.VERIFY_LEVELS = VERIFY_LEVELS;

module.exports = VerifiableCredentialBaseConstructor;
