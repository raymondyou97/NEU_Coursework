import apiFetch, {
  postJson,
  deleteRequest,
  putRequest,
} from '../util/apiFetch';

export default class ServiceQuestionService {
  static instance = null;

  static getInstance() {
    if (ServiceQuestionService.instance === null) {
      ServiceQuestionService.instance = new ServiceQuestionService();
    }
    return this.instance;
  }

  findServiceQuestionById = id =>
    apiFetch(`/api/serviceQuestions/${id}`).then(response => response.json());

  findAllServiceQuestions = () =>
    apiFetch('/api/serviceQuestions').then(response => response.json());

  findPagedServiceQuestions = (page, count) =>
    apiFetch(`/api/serviceQuestions/paged?page=${page}&count=${count}`).then(
      response => response.json()
    );

  createServiceQuestion = data =>
    postJson('/api/serviceQuestions', data).then(response => response.json());

  deleteServiceQuestion = id => deleteRequest(`/api/serviceQuestions/${id}`);

  updateServiceQuestion = (id, data) =>
    putRequest(`/api/serviceQuestions/${id}`, data).then(response =>
      response.json()
    );
}
