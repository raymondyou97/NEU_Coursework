import apiFetch, {
  postJson,
  deleteRequest,
  putRequest,
} from '../util/apiFetch';

export default class ServiceService {
  static instance = null;

  static getInstance() {
    if (ServiceService.instance === null) {
      ServiceService.instance = new ServiceService();
    }
    return this.instance;
  }

  findServiceById = serviceId =>
    apiFetch(`/api/services/${serviceId}`).then(response => response.json());

  findAllServices = () =>
    apiFetch(`/api/services/`).then(response => response.json());

  findAllProvidersForService = id =>
    apiFetch(`/api/services/${id}/users`).then(response => response.json());

  findAllServiceQuestionsForService = id =>
    apiFetch(`/api/services/${id}/questions`).then(response => response.json());

  search = (term, zip) =>
    apiFetch(`/api/services/query?term=${term}&zip=${zip}`).then(response =>
      response.json()
    );

  createService = data =>
    postJson('/api/services', data).then(response => response.json());

  deleteService = id => deleteRequest(`/api/services/${id}`);

  updateService = (id, data) =>
    putRequest(`/api/services/${id}`, data).then(response => response.json());
}
