import apiFetch, {
  deleteRequest,
  postJson,
  putRequest,
} from '../util/apiFetch';

export default class UserService {
  static instance = null;

  static getInstance() {
    if (UserService.instance === null) {
      UserService.instance = new UserService();
    }
    return this.instance;
  }

  findUserById = userId =>
    apiFetch(`/api/users/${userId}`).then(response => response.json());

  findUserByUsername = username =>
    apiFetch(`/api/users/query?username=${username}`)
      .then(response => response.json())
      .catch(err => err);

  findAllUsers = () => apiFetch('/api/users').then(response => response.json());

  findUsersForSearch = searchCriteria =>
    postJson(`/api/users/search`, searchCriteria).then(response =>
      response.json()
    );

  deleteUser = id => deleteRequest(`/api/users/${id}`);

  createUser = data =>
    postJson('/api/users', data).then(response => response.json());

  updateUser = (id, data) =>
    putRequest(`/api/users/${id}`, data).then(response => response.json());
}
