/* eslint-disable no-template-curly-in-string */
// ######################################### DEFINITIONS ###########################################


// That in consideration that this model is inpired by C++ language data definitions
// Changed: to lower case pattern UCA to Uca
const definitions = [
  {
    identifier: 'civ:Random:node',
    version: '1',
    type: 'String',
    attestable: true,
  },
  {
    identifier: 'civ:Identity:name.first',
    version: '1',
    type: 'String',
    credentialItem: true,
    required: true,
  },
  {
    identifier: 'civ:Identity:firstName',
    version: '1',
    type: 'String',
    credentialItem: true,
    alsoKnown: ['civ:Identity:name.first'],
  },
  {
    identifier: 'civ:Identity:givenName',
    version: '1',
    type: 'String',
    credentialItem: true,
    alsoKnown: ['civ:Identity:name.first'],
  },
  {
    identifier: 'civ:Identity:name.middle',
    version: '1',
    type: 'String',
    credentialItem: true,
  },
  {
    identifier: 'civ:Identity:name.last',
    version: '1',
    type: 'String',
    credentialItem: true,
  },
  {
    identifier: 'civ:Identity:name.nickname',
    version: '1',
    type: 'String',
    credentialItem: true,
  },
  {
    identifier: 'civ:Identity:name.username',
    version: '1',
    type: 'String',
    credentialItem: true,
    alsoKnown: ['civ:Identity:name.nickname'], // We can create alias (more precise dataSources)
  },
  {
    identifier: 'civ:Type:ShortToken', // We can create a Typedef that don't have an identifier. This means it't not a UCA but this is helpful to DRY
    version: '1',
    type: 'String',
    pattern: '/^\\d{5}$/', // We can specify a constraint to define the type domain
    credentialItem: false,
  },
  {
    identifier: 'civ:Verify:phoneNumber.Token',
    version: '1',
    type: 'civ:Type:ShortToken',
    credentialItem: false, // An example on UCA that only relates with the user in short term
  },
  {
    identifier: 'civ:Verify:email.Token',
    version: '1',
    type: 'civ:Type:ShortToken',
    credentialItem: false,
  },
  {
    identifier: 'civ:Type:DocumentType',
    version: '1',
    type: 'String', // change to Array and change the constructor and SchemaGenerator
    credentialItem: false,
  },
  {
    identifier: 'civ:Identity:name', // We can define a new identifier and the structure at same definition
    version: '1',
    type: {
      properties: [{
        name: 'first', // We need a key for templating and regex
        type: 'civ:Identity:name.first', // OR a type
      },
      {
        name: 'middle',
        type: 'civ:Identity:name.middle',
      },
      {
        name: 'last',
        type: 'civ:Identity:name.last',
      },
      {
        name: 'nickname',
        type: 'civ:Identity:name.nickname',
      },
      ],
      required: ['first'],
    },
    credentialItem: true,
  },
  {
    identifier: 'civ:Type:Day',
    version: '1',
    type: 'Number',
    minimum: 0,
    exclusiveMinimum: true,
    maximum: 32,
    exclusiveMaximum: true,
  },
  {
    identifier: 'civ:Type:Month',
    version: '1',
    type: 'Number',
    minimum: 0,
    exclusiveMinimum: true,
    maximum: 13,
    exclusiveMaximum: true,
  },
  {
    identifier: 'civ:Type:Year',
    version: '1',
    type: 'Number',
    minimum: 0,
    exclusiveMinimum: true,
  },
  {
    identifier: 'civ:Type:Date',
    version: '1',
    type: {
      properties: [{
        name: 'day',
        type: 'civ:Type:Day',
      },
      {
        name: 'month',
        type: 'civ:Type:Month',
      },
      {
        name: 'year',
        type: 'civ:Type:Year',
      }],
      required: ['day', 'month', 'year'],
    },
  },
  {
    identifier: 'civ:Identity:DateOfBirth',
    version: '1',
    type: 'civ:Type:Date', // TODO the sample json still generates with a compound object, instead of direct properties
    credentialItem: true,
  },
  {
    identifier: 'civ:Type:Address.street',
    version: 'v1',
    type: 'String',
  },

  {
    identifier: 'civ:Type:Address.unit',
    version: 'v1',
    type: 'String',
  },

  {
    identifier: 'civ:Type:Address.city',
    version: 'v1',
    type: 'String',
  },

  {
    identifier: 'civ:Type:Address.zipCode',
    version: 'v1',
    type: 'String',
  },

  {
    identifier: 'civ:Type:Address.state',
    version: 'v1',
    type: 'String',
  },

  {
    identifier: 'civ:Type:Address.county',
    version: 'v1',
    type: 'String',
  },

  {
    identifier: 'civ:Type:Address.country',
    version: 'v1',
    type: 'String',
  },

  {
    identifier: 'civ:Type:Address',
    version: '1',
    type: {
      properties: [
        {
          name: 'street',
          type: 'civ:Type:Address.street',
        },
        {
          name: 'unit',
          type: 'civ:Type:Address.unit',
        },
        {
          name: 'city',
          type: 'civ:Type:Address.city',
        },
        {
          name: 'zipCode',
          type: 'civ:Type:Address.zipCode',
        },
        {
          name: 'state',
          type: 'civ:Type:Address.state',
        },
        {
          name: 'county',
          type: 'civ:Type:Address.county',
        },
        {
          name: 'country',
          type: 'civ:Type:Address.country',
        },
      ],
      required: ['country'],
    },
    credentialItem: true,
  },
  {
    identifier: 'civ:Type:Email',
    version: '1',
    type: {
      properties: [{
        name: 'user',
        type: 'String',
      },
      {
        name: 'domain',
        type: 'String',
      }],
      required: ['user', 'domain'],
    },
  },

  {
    identifier: 'civ:Contact:personal',
    version: 'v1',
    type: 'civ:Type:Address',
  },
];

module.exports = definitions;
