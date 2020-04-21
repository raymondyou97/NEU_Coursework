# Gregslist Frontend

Here's some useful info.

## Getting Started

1. Install NPM (Google it)
2. `npm install` in the repo root
3. Write code

## Making API Requests

```js
import apiFetch from 'util/apiFetch';

apiFetch('/your/endpoint').then(response => response.json());
```

## Prettier

Prettier is a code formatter for JS. It's in our dev dependencies, which means it'll be installed when you run `npm install`. You can set up your editor to automatically format your code, which is neato.
