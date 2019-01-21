/**
 * name: 'attgenericId',
 * name: 'attBaseIdentity',
 * name: 'attAddress',
 * @type {*[]}
 */
const definitions = [
  {
    identifier: 'credential-cvc:Email-v1',
    version: '1',
    depends: [
      'claim-cvc:Contact.email-v1',
    ],
  },
  {
    identifier: 'credential-cvc:PhoneNumber-v1',
    version: '1',
    depends: [
      'claim-cvc:Contact.phoneNumber-v1',
    ],
  },
  {
    identifier: 'credential-cvc:GenericDocumentId-v1',
    version: '1',
    depends: [
      'claim-cvc:Document.type-v1',
      'claim-cvc:Document.number-v1',
      'claim-cvc:Document.name-v1',
      'claim-cvc:Document.gender-v1',
      'claim-cvc:Document.issueLocation-v1',
      'claim-cvc:Document.issueAuthority-v1',
      'claim-cvc:Document.issueCountry-v1',
      'claim-cvc:Document.placeOfBirth-v1',
      'claim-cvc:Document.dateOfBirth-v1',
      'claim-cvc:Document.address-v1',
      'claim-cvc:Document.properties-v1',
      'cvc:Document:image',
    ],
  },
  {
    identifier: 'credential-cvc:Address-v1',
    version: '1',
    depends: [
      'claim-cvc:Identity.address-v1',
    ],
  },
  {
    identifier: 'credential-cvc:Identity-v1',
    version: '1',
    depends: [
      'claim-cvc:Identity.name-v1',
      'claim-cvc:Identity.dateOfBirth-v1',
    ],
  },
  {
    identifier: 'credential-IDaaS-v1',
    version: '1',
    depends: [
      'claim-cvc:Identity.name-v1',
      'claim-cvc:Identity.dateOfBirth-v1',
      'claim-cvc:Identity.address-v1',
      'claim-cvc:Contact.email-v1',
      'claim-cvc:SocialSecurity.number-v1',
      'claim-cvc:Contact.phoneNumber-v1',
    ],
  },
];

module.exports = definitions;
