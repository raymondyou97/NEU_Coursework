// This is here in case we need to implement some custom logic on every request
const apiFetch = (route, ...args) => fetch(`${route}`, ...args);

export const postJson = (route, data) =>
  apiFetch(route, {
    method: 'POST',
    headers: {
      'Content-Type': 'application/json',
    },
    body: JSON.stringify(data),
  });

export const deleteRequest = route =>
  apiFetch(route, {
    method: 'DELETE',
  });

export const putRequest = (route, data) =>
  apiFetch(route, {
    method: 'PUT',
    headers: {
      'Content-Type': 'application/json',
    },
    body: JSON.stringify(data),
  });

export default apiFetch;
