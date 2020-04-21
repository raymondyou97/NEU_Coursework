import apiFetch, {
  deleteRequest,
  postJson,
  putRequest,
} from '../util/apiFetch';

export default class ServiceAnswerService {
  static instance = null;
  static getInstance() {
    if (ServiceAnswerService.instance === null) {
      ServiceAnswerService.instance = new ServiceAnswerService();
    }
    return this.instance;
  }

  findServiceAnswerById = id =>
    apiFetch(`/api/serviceAnswers/${id}`).then(response => response.json());

  findAllServiceAnswers = () =>
    apiFetch('/api/serviceAnswers').then(response => response.json());

  findPagedServiceAnswers = (page, count) =>
    apiFetch(`/api/serviceAnswers/paged?page=${page}&count=${count}`).then(
      response => response.json()
    );

  createServiceAnswer = data =>
    postJson('/api/serviceAnswers', data).then(response => response.json());

  updateServiceAnswer = (id, data) =>
    putRequest(`/api/serviceAnswers/${id}`, data).then(response =>
      response.json()
    );

  deleteServiceAnswer = id => deleteRequest(`/api/serviceAnswers/${id}`);
}
